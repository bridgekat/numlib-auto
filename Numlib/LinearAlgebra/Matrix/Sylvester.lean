/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Numlib.Analysis.Matrix.OperatorNorm

/-!
# The Sylvester equation and the separation of two matrices

Let $A$ be an $m \times m$ matrix and $B$ an $n \times n$ matrix. The **Sylvester operator** is the
linear map $X \mapsto A X - X B$ on $m \times n$ matrices, and the **Sylvester equation** is
$A X - X B = C$. The **separation** of $A$ and $B$ is
$$\operatorname{sep}(A, B) = \min_{\|X\|_F = 1} \|A X - X B\|_F,$$
the least value of the Frobenius norm of the Sylvester operator on the Frobenius unit sphere. These
are §7.1.5 and (7.2.5) of [golub2013matrix].

Over any field, the Sylvester operator is bijective when the characteristic polynomials of $A$ and
$B$ are coprime. Over an algebraically closed field, this holds if and only if $A$ and $B$ have no
common eigenvalue (Lemma 7.1.5 of [golub2013matrix]). A solution of a Sylvester equation removes the
off-diagonal block of a block upper triangular matrix by a similarity, and repeating this step gives
the block diagonal decomposition of Theorem 7.1.6 of [golub2013matrix]. The separation is attained,
positive exactly when the Sylvester operator is injective, at most the distance between any
eigenvalue of $A$ and any eigenvalue of $B$, unitarily invariant, 1-Lipschitz in each argument, and
symmetric: $\operatorname{sep}(A, B) = \operatorname{sep}(B, A)$. For Hermitian $A$ and $B$ it is
the distance between the spectra.

## Main definitions

* `Matrix.sylvesterMap`: the Sylvester operator $X \mapsto A X - X B$.
* `Matrix.sep`: the separation $\operatorname{sep}(A, B)$ of (7.2.5) of [golub2013matrix].

## Main results

* `Matrix.aeval_mul_eq_mul_aeval_of_mul_eq_mul`: if $A X = X B$, then $p(A) X = X p(B)$ for every
  polynomial $p$.
* `Matrix.sylvesterMap_injective_of_isCoprime`, `Matrix.existsUnique_sylvesterMap_eq_of_isCoprime`:
  over any field, if $\chi_A$ and $\chi_B$ are coprime, the Sylvester equation has exactly one
  solution for every right-hand side.
* `Matrix.sylvesterMap_bijective_iff_disjoint_spectrum`: over an algebraically closed field, the
  Sylvester operator is bijective if and only if $A$ and $B$ have disjoint spectra, as in Lemma
  7.1.5 of [golub2013matrix].
* `Matrix.isCoprime_charpoly_iff_disjoint_spectrum_complexify`: two real matrices have coprime
  characteristic polynomials if and only if their complexifications have disjoint spectra.
* `Matrix.exists_fromBlocks_conj_eq_fromBlocks_zero`: a solution of $T_{11} Z - Z T_{22} = -T_{12}$
  gives a similarity that removes the off-diagonal block, as in Lemma 7.1.5 of [golub2013matrix].
* `Matrix.exists_isUnit_conj_eq_blockDiagonalPart`: a block upper triangular matrix whose diagonal
  blocks have pairwise disjoint spectra is similar to its block diagonal part, as in Theorem 7.1.6
  of [golub2013matrix].
* `Matrix.sylvesterMap_diagonal_eq_iff`, `Matrix.apply_eq_of_sylvesterMap_diagonal_eq`: with
  diagonal coefficients, the Sylvester equation is solved by entrywise division. This is the solve
  in an eigenvector basis behind the fast Poisson solver of [golub2013matrix] §4.8.4, and the
  description of Cauchy-like matrices by generators in (12.1.4) of [golub2013matrix].
* `Matrix.exists_sep_eq`, `Matrix.sep_mul_norm_le`: the minimum in the definition of the separation
  is attained, and $\operatorname{sep}(A, B) \|X\|_F \le \|A X - X B\|_F$ for every $X$.
* `Matrix.sep_pos_iff`, `Matrix.sep_pos_iff_disjoint_spectrum`: the separation is positive if and
  only if the Sylvester operator is injective, and over $\mathbb{C}$ if and only if the spectra are
  disjoint.
* `Matrix.frobenius_norm_le_div_sep`: the bound $\|X\|_F \le \|A X - X B\|_F / \operatorname{sep}(A,
  B)$, (7.3.20) of [golub2013matrix].
* `Matrix.sep_le_norm_sub`: $\operatorname{sep}(A, B) \le |\alpha - \beta|$ for all eigenvalues
  $\alpha$ of $A$ and $\beta$ of $B$.
* `Matrix.sep_unitary_conj`, `Matrix.sep_sub_le_sep_add`: the separation is unitarily invariant and
  1-Lipschitz in each argument.
* `Matrix.sep_comm`: the separation is symmetric.
* `Matrix.IsHermitian.sep_eq_iInf_abs_eigenvalues_sub`: for Hermitian $A$ and $B$, the separation is
  $\min_{i,j} |\lambda_i(A) - \lambda_j(B)|$.
* `Matrix.sep_eq_iInf_colSingularValues`: the separation of a scalar $c$ and a square matrix $T$ is
  the least singular value of $T - c I$.

## Proof outline

Assume that $\chi_A$ and $\chi_B$ are coprime, and let $A X = X B$. Then $p(A) X = X p(B)$ for every
polynomial $p$. For $p = \chi_A$ the left side is zero by the Cayley–Hamilton theorem. A Bézout
identity $u \chi_A + v \chi_B = 1$ shows that $\chi_A(B)$ is invertible, so $X = 0$. Conversely, a
common eigenvalue $\lambda$, with $A x = \lambda x$ and $y^T B = \lambda y^T$, puts $x y^T$ in the
kernel of the Sylvester operator.

The symmetry of the separation is the one result that is not direct. The perturbation theory of
invariant subspaces inverts the operator $P \mapsto P A - B P$. Through $P \mapsto P^H$, this
operator is the negative of the adjoint of the Sylvester operator of $(A^H, B^H)$, not the Sylvester
operator of $(A, B)$. The proof shows with the Frobenius trace pairing that a lower bound
$c \|X\|_F \le \|A X - X B\|_F$ passes to the adjoint, and then uses $\operatorname{sep}(A^H, B^H) =
\operatorname{sep}(B, A)$.

## Implementation notes

* The Sylvester operator is defined over a commutative ring, and the separation over an `RCLike`
  field. The Frobenius norm comes from the scoped instance `Matrix.Norms.Frobenius`.
* The separation is an infimum over the unit sphere. Its value is $0$ when $m$ or $n$ is empty,
  because the infimum of an empty family of reals is $0$.
* Every result except those on the separation is a statement about the map $X \mapsto A X - X B$ on
  linear maps $F \to E$, for endomorphisms $A$ of $E$ and $B$ of $F$, and the matrix map is its
  coordinate form. Over $\mathbb{C}$ the operator version is Rosenblum's theorem $\sigma(X \mapsto A
  X - X B) \subseteq \sigma(A) - \sigma(B)$, which holds in any Banach algebra.
* The separation is defined here, and not with the theory of invariant subspaces, because it is a
  property of the Sylvester operator alone. All its users (perturbation of invariant subspaces,
  orthogonal iteration, block diagonalization, the conditioning of the Sylvester equation) import
  this module.
* Mathlib's `Polynomial.sylvester` is the Sylvester matrix of two polynomials, which is a different
  object.
-/

open Polynomial

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n]

section CommRing

variable {R : Type*} [CommRing R]

/-- The **Sylvester operator** of a square $m \times m$ matrix $A$ and a square $n \times n$ matrix
$B$ over a commutative ring: the linear map
$$X \mapsto A X - X B$$
on $m \times n$ matrices. This is the operator of the Sylvester equation in [golub2013matrix]
§7.1.5. -/
def sylvesterMap (A : Matrix m m R) (B : Matrix n n R) : Matrix m n R →ₗ[R] Matrix m n R where
  toFun X := A * X - X * B
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul]; abel
  map_smul' c X := by simp [Matrix.mul_smul, Matrix.smul_mul, smul_sub]

/-- The Sylvester operator of $A$ and $B$ maps $X$ to $A X - X B$. -/
@[simp]
theorem sylvesterMap_apply (A : Matrix m m R) (B : Matrix n n R) (X : Matrix m n R) :
    sylvesterMap A B X = A * X - X * B :=
  rfl

/-- **Intertwining passes to polynomials.** Let $A$ be an $m \times m$ matrix, $B$ an $n \times n$
matrix and $X$ an $m \times n$ matrix over a commutative ring. If $A X = X B$, then
$$p(A) X = X p(B)$$
for every polynomial $p$. -/
theorem aeval_mul_eq_mul_aeval_of_mul_eq_mul [DecidableEq m] [DecidableEq n]
    {A : Matrix m m R} {B : Matrix n n R} {X : Matrix m n R} (h : A * X = X * B) (p : R[X]) :
    aeval A p * X = X * aeval B p := by
  have hpow : ∀ k : ℕ, A ^ k * X = X * B ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]
  simp only [aeval_eq_sum_range, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul,
    Matrix.mul_smul, hpow]

/-- **The Sylvester operator on a rank-one matrix of eigenvectors.** Let $x$ and $y$ be vectors with
$A x = \alpha x$ and $y^T B = \beta y^T$. Then
$$A (x y^T) - (x y^T) B = (\alpha - \beta)\, x y^T.$$
-/
theorem sylvesterMap_vecMulVec {A : Matrix m m R} {B : Matrix n n R} {x : m → R} {y : n → R}
    {α β : R} (hx : A *ᵥ x = α • x) (hy : y ᵥ* B = β • y) :
    sylvesterMap A B (vecMulVec x y) = (α - β) • vecMulVec x y := by
  rw [sylvesterMap_apply, mul_vecMulVec, vecMulVec_mul, hx, hy, smul_vecMulVec, vecMulVec_smul,
    sub_smul]

/-- **A common eigenvalue gives a kernel element of the Sylvester operator.** Let $x$ and $y$ be
vectors with $A x = c x$ and $y^T B = c y^T$. Then
$$A (x y^T) - (x y^T) B = 0.$$
This is a step of the proof of Lemma 7.1.5 of [golub2013matrix], with $y^T$ in place of $y^H$.

The rank-one matrix $x y^T$ is `Matrix.vecMulVec x y`. The vectors may be zero. -/
theorem sylvesterMap_vecMulVec_eq_zero {A : Matrix m m R} {B : Matrix n n R} {x : m → R}
    {y : n → R} {c : R} (hx : A *ᵥ x = c • x) (hy : y ᵥ* B = c • y) :
    sylvesterMap A B (vecMulVec x y) = 0 := by
  rw [sylvesterMap_vecMulVec hx hy, sub_self, zero_smul]

/-- **Change of bases.** Let $P$ and $Q$ be invertible square matrices over a commutative ring.
Conjugating both coefficients conjugates the Sylvester operator:
$$(P F P^{-1})(P A Q^{-1}) - (P A Q^{-1})(Q G Q^{-1}) = P\, (F A - A G)\, Q^{-1}.$$
This is used in [golub2013matrix] §12.1.6 and §12.1.8. -/
theorem sylvesterMap_conj [DecidableEq m] [DecidableEq n] {P : Matrix m m R} {Q : Matrix n n R}
    (hP : IsUnit P) (hQ : IsUnit Q) (F : Matrix m m R) (G : Matrix n n R) (A : Matrix m n R) :
    sylvesterMap (P * F * P⁻¹) (Q * G * Q⁻¹) (P * A * Q⁻¹) = P * sylvesterMap F G A * Q⁻¹ := by
  have hP' : P⁻¹ * P = 1 := nonsing_inv_mul P ((isUnit_iff_isUnit_det P).mp hP)
  have hQ' : Q⁻¹ * Q = 1 := nonsing_inv_mul Q ((isUnit_iff_isUnit_det Q).mp hQ)
  simp only [sylvesterMap_apply, Matrix.mul_sub, Matrix.sub_mul]
  congr 1
  · calc P * F * P⁻¹ * (P * A * Q⁻¹) = P * F * (P⁻¹ * P) * A * Q⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = P * (F * A) * Q⁻¹ := by rw [hP', Matrix.mul_one, Matrix.mul_assoc P]
  · calc P * A * Q⁻¹ * (Q * G * Q⁻¹) = P * A * (Q⁻¹ * Q) * G * Q⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = P * (A * G) * Q⁻¹ := by rw [hQ', Matrix.mul_one, Matrix.mul_assoc P]

/-- **Reindexing.** Let $\sigma$ and $\tau$ be bijections of the index sets. Permuting the rows and
columns of $F$ by $\sigma$, of $G$ by $\tau$, and of $A$ by $\sigma$ and $\tau$ permutes the
rows and columns of $F A - A G$ in the same way. This is the pivoting of a displacement equation
in Algorithm 12.1.2 of [golub2013matrix]. -/
theorem sylvesterMap_submatrix {m' n' : Type*} [Fintype m'] [Fintype n'] (σ : m' ≃ m)
    (τ : n' ≃ n) (F : Matrix m m R) (G : Matrix n n R) (A : Matrix m n R) :
    sylvesterMap (F.submatrix σ σ) (G.submatrix τ τ) (A.submatrix σ τ) =
      (sylvesterMap F G A).submatrix σ τ := by
  rw [sylvesterMap_apply, sylvesterMap_apply, submatrix_mul_equiv, submatrix_mul_equiv]
  rfl

/-- With diagonal coefficients the Sylvester operator acts entrywise:
$$\bigl(\operatorname{diag}(\omega) X - X \operatorname{diag}(\nu)\bigr)_{kj} = (\omega_k -
  \nu_j)\, x_{kj}.$$
-/
theorem sylvesterMap_diagonal_apply [DecidableEq m] [DecidableEq n] (ω : m → R) (ν : n → R)
    (X : Matrix m n R) (k : m) (j : n) :
    sylvesterMap (diagonal ω) (diagonal ν) X k j = (ω k - ν j) * X k j := by
  simp only [sylvesterMap_apply, Matrix.sub_apply, diagonal_mul, mul_diagonal]
  ring

/-! ### The block computation of Lemma 7.1.5 -/

/-- **The block computation of Lemma 7.1.5** of [golub2013matrix]. For square blocks $T_{11}$ and
$T_{22}$ and rectangular blocks $T_{12}$ and $Z$ over a commutative ring,
$$\begin{bmatrix} I & -Z \\ 0 & I \end{bmatrix} \begin{bmatrix} T_{11} & T_{12} \\ 0 & T_{22}
  \end{bmatrix} \begin{bmatrix} I & Z \\ 0 & I \end{bmatrix} = \begin{bmatrix} T_{11} & T_{11}
  Z - Z T_{22} + T_{12} \\ 0 & T_{22} \end{bmatrix}.$$
-/
theorem fromBlocks_one_neg_mul_fromBlocks_mul_fromBlocks_one [DecidableEq m] [DecidableEq n]
    (T₁₁ : Matrix m m R) (T₁₂ : Matrix m n R) (T₂₂ : Matrix n n R) (Z : Matrix m n R) :
    fromBlocks 1 (-Z) 0 1 * fromBlocks T₁₁ T₁₂ 0 T₂₂ * fromBlocks 1 Z 0 1 =
      fromBlocks T₁₁ (T₁₁ * Z - Z * T₂₂ + T₁₂) 0 T₂₂ := by
  simp only [fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
    Matrix.mul_zero, Matrix.neg_mul, add_zero, zero_add]
  congr 1
  abel

/-- The block matrix $\begin{bmatrix} I & -Z \\ 0 & I \end{bmatrix}$ is the inverse of
$\begin{bmatrix} I & Z \\ 0 & I \end{bmatrix}$: their product is $I$. -/
theorem fromBlocks_one_neg_mul_fromBlocks_one [DecidableEq m] [DecidableEq n]
    (Z : Matrix m n R) :
    fromBlocks (1 : Matrix m m R) (-Z) (0 : Matrix n m R) (1 : Matrix n n R) *
      fromBlocks 1 Z 0 1 = 1 := by
  simp [fromBlocks_multiply, fromBlocks_one]

/-- **Lemma 7.1.5** of [golub2013matrix], removal of the off-diagonal block. Let $T_{11}$ and
$T_{22}$ be square matrices over a commutative ring such that the Sylvester operator
$X \mapsto T_{11} X - X T_{22}$ is surjective, for instance because their spectra are disjoint.
Then for every $T_{12}$ there is a matrix $Z$ with $T_{11} Z - Z T_{22} = -T_{12}$ such that
$Y = \begin{bmatrix} I & Z \\ 0 & I \end{bmatrix}$ is invertible and
$$Y^{-1} \begin{bmatrix} T_{11} & T_{12} \\ 0 & T_{22} \end{bmatrix} Y = \begin{bmatrix} T_{11}
  & 0 \\ 0 & T_{22} \end{bmatrix}.$$
-/
theorem exists_fromBlocks_conj_eq_fromBlocks_zero [DecidableEq m] [DecidableEq n]
    {T₁₁ : Matrix m m R} {T₂₂ : Matrix n n R} (h : Function.Surjective (sylvesterMap T₁₁ T₂₂))
    (T₁₂ : Matrix m n R) :
    ∃ Z : Matrix m n R, T₁₁ * Z - Z * T₂₂ = -T₁₂ ∧
      IsUnit (fromBlocks (1 : Matrix m m R) Z (0 : Matrix n m R) (1 : Matrix n n R)) ∧
      (fromBlocks (1 : Matrix m m R) Z (0 : Matrix n m R) (1 : Matrix n n R))⁻¹ *
          fromBlocks T₁₁ T₁₂ 0 T₂₂ * fromBlocks (1 : Matrix m m R) Z 0 1 =
        fromBlocks T₁₁ 0 0 T₂₂ := by
  obtain ⟨Z, hZ⟩ := h (-T₁₂)
  rw [sylvesterMap_apply] at hZ
  have hinv := fromBlocks_one_neg_mul_fromBlocks_one Z
  have hY : (fromBlocks (1 : Matrix m m R) Z (0 : Matrix n m R) (1 : Matrix n n R))⁻¹ =
      fromBlocks 1 (-Z) 0 1 := inv_eq_left_inv hinv
  refine ⟨Z, hZ, (isUnit_iff_isUnit_det _).mpr (isUnit_det_of_left_inverse hinv), ?_⟩
  rw [hY, fromBlocks_one_neg_mul_fromBlocks_mul_fromBlocks_one, hZ, neg_add_cancel]

end CommRing

/-! ### Unique solvability over a field -/

section Field

variable {K : Type*} [Field K] [DecidableEq m] [DecidableEq n]

/-- **Coprime characteristic polynomials make the Sylvester operator injective.** Let $A$ and $B$ be
square matrices over a field. If the characteristic polynomials $\chi_A$ and $\chi_B$ are
coprime, then $X \mapsto A X - X B$ is injective. This is Lemma 7.1.5 of [golub2013matrix] in a
form that holds over any field.

The proof uses `Matrix.aeval_mul_eq_mul_aeval_of_mul_eq_mul` with $p = \chi_A$, the
Cayley–Hamilton theorem, and a Bézout identity $u \chi_A + v \chi_B = 1$, which makes
$\chi_A(B)$ invertible. -/
theorem sylvesterMap_injective_of_isCoprime {A : Matrix m m K} {B : Matrix n n K}
    (h : IsCoprime A.charpoly B.charpoly) : Function.Injective (sylvesterMap A B) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro X hX
  rw [sylvesterMap_apply, sub_eq_zero] at hX
  have h0 : X * aeval B A.charpoly = 0 := by
    rw [← aeval_mul_eq_mul_aeval_of_mul_eq_mul hX, aeval_self_charpoly, Matrix.zero_mul]
  obtain ⟨u, v, huv⟩ := h
  have h1 : aeval B A.charpoly * aeval B u = 1 := by
    have := congrArg (aeval B) huv
    rw [map_add, map_mul, map_mul, aeval_self_charpoly, Matrix.mul_zero, add_zero,
      map_one] at this
    rw [← this, ← map_mul, ← map_mul, mul_comm]
  calc X = X * (aeval B A.charpoly * aeval B u) := by rw [h1, Matrix.mul_one]
    _ = 0 := by rw [← Matrix.mul_assoc, h0, Matrix.zero_mul]

/-- Let $A$ and $B$ be square matrices over a field. If $\chi_A$ and $\chi_B$ are coprime, then the
Sylvester operator $X \mapsto A X - X B$ is bijective.

An injective endomorphism of a finite-dimensional vector space is surjective. -/
theorem sylvesterMap_bijective_of_isCoprime {A : Matrix m m K} {B : Matrix n n K}
    (h : IsCoprime A.charpoly B.charpoly) : Function.Bijective (sylvesterMap A B) :=
  have hi := sylvesterMap_injective_of_isCoprime h
  ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

/-- Let $A$ and $B$ be square matrices over a field. If $\chi_A$ and $\chi_B$ are coprime, then for
every $C$ the Sylvester equation
$$A X - X B = C$$
has exactly one solution $X$. -/
theorem existsUnique_sylvesterMap_eq_of_isCoprime {A : Matrix m m K} {B : Matrix n n K}
    (h : IsCoprime A.charpoly B.charpoly) (C : Matrix m n K) :
    ∃! X : Matrix m n K, A * X - X * B = C := by
  simpa only [sylvesterMap_apply] using (sylvesterMap_bijective_of_isCoprime h).existsUnique C

/-- Let $A$ be a square matrix over a field, and let $\mu$ be in the spectrum of $A$. Then $A$ has a
left eigenvector for $\mu$: there is a vector $y \neq 0$ with $y^T A = \mu y^T$. -/
theorem exists_vecMul_eq_smul_of_mem_spectrum {A : Matrix n n K} {μ : K}
    (hμ : μ ∈ spectrum K A) : ∃ y, y ≠ 0 ∧ y ᵥ* A = μ • y := by
  rw [← spectrum_transpose, mem_spectrum_iff_exists_mulVec_eq_smul] at hμ
  obtain ⟨y, hy, hyA⟩ := hμ
  exact ⟨y, hy, by rw [← mulVec_transpose, hyA]⟩

/-- Let $A$ and $B$ be square matrices over an algebraically closed field. Then $\chi_A$ and
$\chi_B$ are coprime if and only if the spectra of $A$ and $B$ are disjoint. -/
theorem isCoprime_charpoly_iff_disjoint_spectrum [IsAlgClosed K] (A : Matrix m m K)
    (B : Matrix n n K) :
    IsCoprime A.charpoly B.charpoly ↔ Disjoint (spectrum K A) (spectrum K B) := by
  rw [isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := K) K, Set.disjoint_left]
  simp only [coe_aeval_eq_eval, mem_spectrum_iff_isRoot_charpoly, IsRoot.def]
  constructor
  · intro h a ha hb
    rcases h a with h | h <;> contradiction
  · intro h a
    by_cases ha : eval a A.charpoly = 0
    · exact Or.inr (h ha)
    · exact Or.inl ha

/-- **Lemma 7.1.5** of [golub2013matrix], unique solvability. Let $A$ and $B$ be square matrices
over an algebraically closed field. Then the Sylvester operator $X \mapsto A X - X B$ is
bijective if and only if $A$ and $B$ have no common eigenvalue:
$$\sigma(A) \cap \sigma(B) = \emptyset.$$

One direction is `Matrix.sylvesterMap_bijective_of_isCoprime` with
`Matrix.isCoprime_charpoly_iff_disjoint_spectrum`. For the other direction, a common eigenvalue
gives the kernel element `Matrix.sylvesterMap_vecMulVec_eq_zero`. -/
theorem sylvesterMap_bijective_iff_disjoint_spectrum [IsAlgClosed K] {A : Matrix m m K}
    {B : Matrix n n K} :
    Function.Bijective (sylvesterMap A B) ↔ Disjoint (spectrum K A) (spectrum K B) := by
  refine ⟨fun h => Set.disjoint_left.mpr fun c hA hB => ?_, fun h =>
    sylvesterMap_bijective_of_isCoprime ((isCoprime_charpoly_iff_disjoint_spectrum A B).mpr h)⟩
  obtain ⟨x, hx, hxA⟩ := (mem_spectrum_iff_exists_mulVec_eq_smul A c).mp hA
  obtain ⟨y, hy, hyB⟩ := exists_vecMul_eq_smul_of_mem_spectrum hB
  have h0 := sylvesterMap_vecMulVec_eq_zero hxA hyB
  rw [← map_zero (sylvesterMap A B)] at h0
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hy
  have := congrFun (congrFun (h.1 h0) i) j
  rw [vecMulVec_apply, Matrix.zero_apply] at this
  exact mul_ne_zero hi hj this

/-- Let $A$ and $B$ be square matrices over an algebraically closed field with disjoint spectra.
Then for every $C$ the Sylvester equation
$$A X - X B = C$$
has exactly one solution $X$. -/
theorem existsUnique_sylvesterMap_eq [IsAlgClosed K] {A : Matrix m m K} {B : Matrix n n K}
    (h : Disjoint (spectrum K A) (spectrum K B)) (C : Matrix m n K) :
    ∃! X : Matrix m n K, A * X - X * B = C := by
  simpa only [sylvesterMap_apply] using
    (sylvesterMap_bijective_iff_disjoint_spectrum.mpr h).existsUnique C

/-- Let $A$ and $B$ be square matrices over an algebraically closed field with disjoint spectra. If
$A X - X B = 0$, then $X = 0$. This is the uniqueness part of
`Matrix.existsUnique_sylvesterMap_eq`. -/
theorem eq_zero_of_mul_sub_mul_eq_zero [IsAlgClosed K] {A : Matrix m m K} {B : Matrix n n K}
    (h : Disjoint (spectrum K A) (spectrum K B)) {X : Matrix m n K} (hX : A * X - X * B = 0) :
    X = 0 :=
  (sylvesterMap_bijective_iff_disjoint_spectrum.mpr h).1
    (by rw [sylvesterMap_apply, hX, map_zero])

/-- **The diagonal Sylvester equation.** Let $\omega$ and $\nu$ be vectors over a field with
$\omega_k \neq \nu_j$ for all $k$ and $j$. Then
$$\operatorname{diag}(\omega) X - X \operatorname{diag}(\nu) = C \iff x_{kj} =
  \frac{c_{kj}}{\omega_k - \nu_j} \text{ for all } k, j.$$
This is the solve of [golub2013matrix] §4.8.4 and (12.1.4). -/
theorem sylvesterMap_diagonal_eq_iff {ω : m → K} {ν : n → K} (h : ∀ k j, ω k ≠ ν j)
    {X C : Matrix m n K} :
    sylvesterMap (diagonal ω) (diagonal ν) X = C ↔ X = of fun k j => C k j / (ω k - ν j) := by
  simp only [← Matrix.ext_iff, sylvesterMap_diagonal_apply, of_apply]
  refine forall_congr' fun k => forall_congr' fun j => ?_
  rw [eq_div_iff (sub_ne_zero.mpr (h k j)), mul_comm, eq_comm]

/-- **Cauchy-like matrices are determined by their generators.** Let $\omega$ and $\nu$ be vectors
over a field with $\omega_k \neq \nu_j$ for all $k$ and $j$, and let $R$ and $S$ be matrices
with $r$ columns, whose rows are $R_k$ and $S_j$. Then
$$\operatorname{diag}(\omega) A - A \operatorname{diag}(\nu) = R S^T \iff a_{kj} = \frac{R_k
  \cdot S_j}{\omega_k - \nu_j} \text{ for all } k, j.$$
This is (12.1.4) of [golub2013matrix]. -/
theorem apply_eq_of_sylvesterMap_diagonal_eq {r : Type*} [Fintype r] {ω : m → K} {ν : n → K}
    (h : ∀ k j, ω k ≠ ν j) {A : Matrix m n K} {R : Matrix m r K} {S : Matrix n r K} :
    sylvesterMap (diagonal ω) (diagonal ν) A = R * Sᵀ ↔
      ∀ k j, A k j = (R k ⬝ᵥ S j) / (ω k - ν j) := by
  rw [sylvesterMap_diagonal_eq_iff h, ← Matrix.ext_iff]
  simp only [of_apply, Matrix.mul_apply, transpose_apply, dotProduct]

end Field

/-- **Real matrices.** Let $A$ and $B$ be real square matrices. Then $\chi_A$ and $\chi_B$ are
coprime if and only if the complexifications of $A$ and $B$ have disjoint spectra.

Coprimality is preserved and reflected by the field extension $\mathbb{R} \subseteq \mathbb{C}$,
and over $\mathbb{C}$ it means that the polynomials have no common root. This result shows that
a real Sylvester equation between blocks of a real Schur form has a unique solution. -/
theorem isCoprime_charpoly_iff_disjoint_spectrum_complexify [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℝ) (B : Matrix n n ℝ) :
    IsCoprime A.charpoly B.charpoly ↔
      Disjoint (spectrum ℂ A.complexify) (spectrum ℂ B.complexify) := by
  rw [← isCoprime_charpoly_iff_disjoint_spectrum, charpoly_complexify, charpoly_complexify,
    isCoprime_map]

/-! ### Block diagonalization -/

section BlockDiagonal

variable {K : Type*} [Field K]

/-- Conjugation commutes with a simultaneous reindexing of rows and columns:
$(Y_e)^{-1} T_e Y_e = (Y^{-1} T Y)_e$, where $M_e$ is $M$ with rows and columns reindexed by
$e$. -/
private theorem inv_mul_mul_submatrix_equiv {p : Type*} [Fintype p] [DecidableEq p]
    [DecidableEq n] (e : p ≃ n) (Y T : Matrix n n K) :
    (Y.submatrix e e)⁻¹ * T.submatrix e e * Y.submatrix e e = (Y⁻¹ * T * Y).submatrix e e := by
  rw [inv_submatrix_equiv, submatrix_mul_equiv, submatrix_mul_equiv]

/-- The two-block step of Theorem 7.1.6 of [golub2013matrix]: if $T$ has no entry from the rows
outside a set $p$ into the columns in $p$, the Sylvester operator of the two diagonal blocks is
surjective, and $Y_1$ is invertible, then $T$ is similar, after the split of the indices into
$p$ and its complement, to $\begin{bmatrix} Y_1^{-1} T_{11} Y_1 & 0 \\ 0 & T_{22}
\end{bmatrix}$. -/
private theorem exists_conj_submatrix_sumCompl [DecidableEq n] (p : n → Prop) [DecidablePred p]
    {T : Matrix n n K} (hT : ∀ i j, ¬p i → p j → T i j = 0)
    (hs : Function.Surjective
      (sylvesterMap (T.toSquareBlockProp p) (T.toSquareBlockProp fun i => ¬p i)))
    {Y₁ : Matrix {i // p i} {i // p i} K} (hY₁ : IsUnit Y₁) :
    ∃ Y : Matrix n n K, IsUnit Y ∧
      (Y⁻¹ * T * Y).submatrix (Equiv.sumCompl p) (Equiv.sumCompl p) =
        fromBlocks (Y₁⁻¹ * T.toSquareBlockProp p * Y₁) 0 0
          (T.toSquareBlockProp fun i => ¬p i) := by
  set e := Equiv.sumCompl p
  set T₁ := T.toSquareBlockProp p
  set T₂ := T.toSquareBlockProp fun i => ¬p i
  have hT' : T.submatrix e e = fromBlocks T₁ (T.toBlock p fun i => ¬p i) 0 T₂ := by
    ext (i | i) (j | j)
    · rfl
    · rfl
    · exact hT _ _ i.2 j.2
    · rfl
  obtain ⟨Z, -, hunit, hconj⟩ := exists_fromBlocks_conj_eq_fromBlocks_zero hs
    (T.toBlock p fun i => ¬p i)
  set V := fromBlocks (1 : Matrix {i // p i} {i // p i} K) Z (0 : Matrix {i // ¬p i} _ K)
    (1 : Matrix {i // ¬p i} {i // ¬p i} K)
  have hY₁' : Y₁⁻¹ * Y₁ = 1 := nonsing_inv_mul Y₁ ((isUnit_iff_isUnit_det Y₁).mp hY₁)
  set W := fromBlocks Y₁ (0 : Matrix {i // p i} {i // ¬p i} K) (0 : Matrix {i // ¬p i} _ K)
    (1 : Matrix {i // ¬p i} {i // ¬p i} K)
  have hWinv : fromBlocks Y₁⁻¹ 0 0 1 * W = 1 := by
    simp [W, fromBlocks_multiply, hY₁', fromBlocks_one]
  have hW : IsUnit W := (isUnit_iff_isUnit_det _).mpr (isUnit_det_of_left_inverse hWinv)
  have hWinv' : W⁻¹ = fromBlocks Y₁⁻¹ 0 0 1 := inv_eq_left_inv hWinv
  refine ⟨(V * W).submatrix e.symm e.symm, (isUnit_submatrix_equiv _ _).mpr (hunit.mul hW), ?_⟩
  have hTe : T = (T.submatrix e e).submatrix e.symm e.symm := by
    simp [submatrix_submatrix]
  rw [hTe, inv_mul_mul_submatrix_equiv, submatrix_submatrix, Equiv.symm_comp_self,
    submatrix_id_id, Matrix.mul_inv_rev, hT']
  calc W⁻¹ * V⁻¹ * fromBlocks T₁ (T.toBlock p fun i => ¬p i) 0 T₂ * (V * W)
      = W⁻¹ * (V⁻¹ * fromBlocks T₁ (T.toBlock p fun i => ¬p i) 0 T₂ * V) * W := by
        simp only [Matrix.mul_assoc]
    _ = fromBlocks (Y₁⁻¹ * T₁ * Y₁) 0 0 T₂ := by
        rw [hconj, hWinv']
        simp [W, fromBlocks_multiply]

/-- **Theorem 7.1.6** of [golub2013matrix] over any field. Let $T$ be a square matrix over a field
that is block upper triangular for a labelling $b$ of the indices by a linearly ordered set.
Assume that the diagonal blocks $T_{kk}$ have pairwise coprime characteristic polynomials. Then
there is an invertible $Y$ such that
$$Y^{-1} T Y = \operatorname{diag}(T_{11}, \dots, T_{qq})$$
is the block diagonal part of $T$.

Block upper triangular is `T.BlockTriangular b`, the diagonal block $T_{kk}$ is
`T.toSquareBlock b k`, and the block diagonal part is `Matrix.blockDiagPart b T`. The proof is
an induction on the size. The last block is split off by
`Matrix.exists_fromBlocks_conj_eq_fromBlocks_zero`: its characteristic polynomial is coprime to
the product of the others, which is the characteristic polynomial of the leading part by
`Matrix.BlockTriangular.charpoly`. The induction hypothesis handles the leading part. -/
theorem exists_isUnit_conj_eq_blockDiagonalPart_of_isCoprime [DecidableEq n] {ι : Type*}
    [LinearOrder ι] {b : n → ι} {T : Matrix n n K} (hT : T.BlockTriangular b)
    (hcop : Pairwise fun k l : ι =>
      IsCoprime (T.toSquareBlock b k).charpoly (T.toSquareBlock b l).charpoly) :
    ∃ Y : Matrix n n K, IsUnit Y ∧ Y⁻¹ * T * Y = blockDiagPart b T := by
  change ∃ Y : Matrix n n K, IsUnit Y ∧ Y⁻¹ * T * Y = of fun i j => if b i = b j then T i j else 0
  induction hN : Fintype.card n using Nat.strong_induction_on generalizing n with
  | _ N ih =>
  by_cases hall : ∀ i j, b i = b j
  · refine ⟨1, isUnit_one, ?_⟩
    ext i j
    simp [hall i j]
  push Not at hall
  obtain ⟨i₀, j₀, hij⟩ := hall
  have hne : (Finset.univ : Finset n).Nonempty := ⟨i₀, Finset.mem_univ _⟩
  set k₀ := Finset.univ.sup' hne b with hk₀
  have hle : ∀ i, b i ≤ k₀ := fun i => Finset.le_sup' b (Finset.mem_univ i)
  obtain ⟨imax, -, himax⟩ := Finset.exists_mem_eq_sup' hne b
  set p : n → Prop := fun i => b i < k₀ with hp
  have hnp : ∀ i, ¬p i ↔ b i = k₀ := fun i => by
    simp only [hp, not_lt]; exact ⟨fun h => le_antisymm (hle i) h, fun h => h.ge⟩
  -- the leading part is smaller
  have hcard : Fintype.card {i // p i} < N := by
    rw [← hN]
    exact Fintype.card_subtype_lt (x := imax) (by rw [hnp]; exact himax.symm)
  set T₁ := T.toSquareBlockProp p
  set T₂ := T.toSquareBlockProp fun i => ¬p i
  have hT₁ : T₁.BlockTriangular (fun i => b i.1) := hT.submatrix
  -- the blocks of the leading part
  have hblock₁ : ∀ k, k < k₀ →
      (T₁.toSquareBlock (fun i => b i.1) k).charpoly = (T.toSquareBlock b k).charpoly := by
    intro k hk
    let f : {x : {i // p i} // b x.1 = k} ≃ {i // b i = k} :=
      { toFun := fun x => ⟨x.1.1, x.2⟩
        invFun := fun x => ⟨⟨x.1, by simp only [hp, x.2, hk]⟩, x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← charpoly_reindex f]
    rfl
  have hempty₁ : ∀ k, ¬k < k₀ → (T₁.toSquareBlock (fun i => b i.1) k).charpoly = 1 := by
    intro k hk
    have : IsEmpty {x : {i // p i} // b x.1 = k} :=
      ⟨fun x => hk (x.2 ▸ x.1.2)⟩
    exact charpoly_isEmpty
  have hblock₂ : T₂.charpoly = (T.toSquareBlock b k₀).charpoly := by
    let f : {i // ¬p i} ≃ {i // b i = k₀} := Equiv.subtypeEquivRight hnp
    rw [← charpoly_reindex f]
    rfl
  -- coprimality of the two parts
  have hcop₁₂ : IsCoprime T₁.charpoly T₂.charpoly := by
    rw [hT₁.charpoly, hblock₂]
    refine IsCoprime.prod_left fun k _ => ?_
    by_cases hk : k < k₀
    · rw [hblock₁ k hk]
      exact hcop hk.ne
    · rw [hempty₁ k hk]
      exact isCoprime_one_left
  have hs := (sylvesterMap_bijective_of_isCoprime hcop₁₂).2
  -- the induction hypothesis on the leading part
  have hcop₁ : Pairwise fun k l : ι => IsCoprime (T₁.toSquareBlock (fun i => b i.1) k).charpoly
      (T₁.toSquareBlock (fun i => b i.1) l).charpoly := by
    intro k l hkl
    by_cases hk : k < k₀
    · by_cases hl : l < k₀
      · rw [hblock₁ k hk, hblock₁ l hl]; exact hcop hkl
      · rw [hempty₁ l hl]; exact isCoprime_one_right
    · rw [hempty₁ k hk]; exact isCoprime_one_left
  obtain ⟨Y₁, hY₁, hconj₁⟩ := ih _ hcard hT₁ hcop₁ rfl
  have hTz : ∀ i j, ¬p i → p j → T i j = 0 := fun i j hi hj =>
    hT (show b j < b i by rw [(hnp i).mp hi]; exact hj)
  obtain ⟨Y, hY, hconj⟩ := exists_conj_submatrix_sumCompl p hTz hs hY₁
  refine ⟨Y, hY, ?_⟩
  have key : (Y⁻¹ * T * Y).submatrix (Equiv.sumCompl p) (Equiv.sumCompl p) =
      (of fun i j => if b i = b j then T i j else 0).submatrix (Equiv.sumCompl p)
        (Equiv.sumCompl p) := by
    rw [hconj, hconj₁]
    ext (i | i) (j | j)
    · rfl
    · have hj := (hnp j.1).mp j.2
      simp [(show b i.1 ≠ b j.1 by rw [hj]; exact i.2.ne)]
    · have hi := (hnp i.1).mp i.2
      simp [(show b i.1 ≠ b j.1 by rw [hi]; exact j.2.ne')]
    · have hi := (hnp i.1).mp i.2
      have hj := (hnp j.1).mp j.2
      simp [toSquareBlockProp_def, hi, hj]
  have := congrArg (fun M => M.submatrix (Equiv.sumCompl p).symm (Equiv.sumCompl p).symm) key
  simpa [submatrix_submatrix] using this

/-- **Theorem 7.1.6** of [golub2013matrix] (block diagonal decomposition). Let $T$ be a square
matrix over an algebraically closed field that is block upper triangular for a labelling $b$ of
the indices by a linearly ordered set. Assume that the diagonal blocks $T_{kk}$ have pairwise
disjoint spectra. Then there is an invertible $Y$ with
$$Y^{-1} T Y = \operatorname{diag}(T_{11}, \dots, T_{qq}).$$

The block diagonal part is `Matrix.blockDiagPart b T`. The proof specializes
`Matrix.exists_isUnit_conj_eq_blockDiagonalPart_of_isCoprime`. -/
theorem exists_isUnit_conj_eq_blockDiagonalPart [DecidableEq n] [IsAlgClosed K] {ι : Type*}
    [LinearOrder ι] {b : n → ι} {T : Matrix n n K} (hT : T.BlockTriangular b)
    (hdisj : Pairwise fun k l : ι =>
      Disjoint (spectrum K (T.toSquareBlock b k)) (spectrum K (T.toSquareBlock b l))) :
    ∃ Y : Matrix n n K, IsUnit Y ∧ Y⁻¹ * T * Y = blockDiagPart b T :=
  exists_isUnit_conj_eq_blockDiagonalPart_of_isCoprime hT fun _ _ hkl =>
    (isCoprime_charpoly_iff_disjoint_spectrum _ _).mpr (hdisj hkl)

end BlockDiagonal

/-! ### The separation -/

section Sep

open scoped Matrix.Norms.Frobenius

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The **separation** of an $m \times m$ matrix $A$ and an $n \times n$ matrix $B$ over
$\mathbb{R}$ or $\mathbb{C}$:
$$\operatorname{sep}(A, B) = \inf_{\|X\|_F = 1} \|A X - X B\|_F,$$
the infimum of the Frobenius norm of the Sylvester operator on the Frobenius unit sphere of
$m \times n$ matrices. This is (7.2.5) of [golub2013matrix], where the infimum is written as a
minimum.

The value is $0$ when $m$ or $n$ is empty, because the infimum of an empty family is $0$. The
infimum is attained otherwise, by `Matrix.exists_sep_eq`. -/
noncomputable def sep (A : Matrix m m 𝕜) (B : Matrix n n 𝕜) : ℝ :=
  ⨅ X : {X : Matrix m n 𝕜 // ‖X‖ = 1}, ‖A * X.1 - X.1 * B‖

variable {A : Matrix m m 𝕜} {B : Matrix n n 𝕜}

/-- The separation is nonnegative: $\operatorname{sep}(A, B) \ge 0$. -/
theorem sep_nonneg (A : Matrix m m 𝕜) (B : Matrix n n 𝕜) : 0 ≤ sep A B :=
  Real.iInf_nonneg fun _ => norm_nonneg _

private theorem bddBelow_range_sep (A : Matrix m m 𝕜) (B : Matrix n n 𝕜) :
    BddBelow (Set.range fun X : {X : Matrix m n 𝕜 // ‖X‖ = 1} => ‖A * X.1 - X.1 * B‖) :=
  ⟨0, by rintro _ ⟨X, rfl⟩; exact norm_nonneg _⟩

/-- If $\|X\|_F = 1$, then $\operatorname{sep}(A, B) \le \|A X - X B\|_F$. -/
theorem sep_le_norm {X : Matrix m n 𝕜} (hX : ‖X‖ = 1) : sep A B ≤ ‖A * X - X * B‖ :=
  ciInf_le (bddBelow_range_sep A B) ⟨X, hX⟩

/-- Let $m, n \ge 1$. If $c \le \|A X - X B\|_F$ for every $X$ with $\|X\|_F = 1$, then
$c \le \operatorname{sep}(A, B)$. -/
theorem le_sep {c : ℝ} [Nonempty m] [Nonempty n]
    (h : ∀ X : Matrix m n 𝕜, ‖X‖ = 1 → c ≤ ‖A * X - X * B‖) : c ≤ sep A B := by
  have : Nonempty {X : Matrix m n 𝕜 // ‖X‖ = 1} :=
    (NormedSpace.sphere_nonempty.mpr zero_le_one).elim fun X hX =>
      ⟨⟨X, mem_sphere_zero_iff_norm.mp hX⟩⟩
  exact le_ciInf fun X => h X.1 X.2

/-- If the Frobenius unit sphere of $m \times n$ matrices is empty, which happens when $m$ or $n$ is
$0$, then $\operatorname{sep}(A, B) = 0$. -/
theorem sep_of_isEmpty [IsEmpty {X : Matrix m n 𝕜 // ‖X‖ = 1}] : sep A B = 0 :=
  Real.iInf_of_isEmpty _

/-- The unit sphere of $m \times n$ matrices is empty, or both index types are nonempty. -/
private theorem isEmpty_or_nonempty_index :
    IsEmpty {X : Matrix m n 𝕜 // ‖X‖ = 1} ∨ (Nonempty m ∧ Nonempty n) := by
  rcases isEmpty_or_nonempty m with hm | hm
  · left
    exact ⟨fun X => by
      have : X.1 = 0 := Matrix.ext fun i _ => (IsEmpty.false i).elim
      simpa [this] using X.2⟩
  rcases isEmpty_or_nonempty n with hn | hn
  · left
    exact ⟨fun X => by
      have : X.1 = 0 := Matrix.ext fun _ j => (IsEmpty.false j).elim
      simpa [this] using X.2⟩
  exact Or.inr ⟨hm, hn⟩

/-- **The separation is the best constant** in the bound
$$\operatorname{sep}(A, B)\, \|X\|_F \le \|A X - X B\|_F,$$
which holds for every $m \times n$ matrix $X$. This is the form
$\min_{X \neq 0} \|A X - X B\|_F / \|X\|_F$ of (7.2.5) of [golub2013matrix]. -/
theorem sep_mul_norm_le (X : Matrix m n 𝕜) : sep A B * ‖X‖ ≤ ‖A * X - X * B‖ := by
  rcases eq_or_ne X 0 with rfl | hX
  · simp
  have hn : 0 < ‖X‖ := norm_pos_iff.mpr hX
  have hY : ‖((‖X‖⁻¹ : ℝ) : 𝕜) • X‖ = 1 := by
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  have h := sep_le_norm (A := A) (B := B) hY
  rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, norm_smul, RCLike.norm_ofReal,
    abs_of_pos (inv_pos.mpr hn)] at h
  calc sep A B * ‖X‖ ≤ ‖X‖⁻¹ * ‖A * X - X * B‖ * ‖X‖ := by gcongr
    _ = ‖A * X - X * B‖ := by field_simp

/-- **The minimum is attained.** Let $m, n \ge 1$. Then there is an $m \times n$ matrix $X$ with
$\|X\|_F = 1$ and
$$\|A X - X B\|_F = \operatorname{sep}(A, B).$$

The Frobenius unit sphere is compact. -/
theorem exists_sep_eq [Nonempty m] [Nonempty n] (A : Matrix m m 𝕜) (B : Matrix n n 𝕜) :
    ∃ X : Matrix m n 𝕜, ‖X‖ = 1 ∧ ‖A * X - X * B‖ = sep A B := by
  have hc : Continuous fun X : Matrix m n 𝕜 => ‖A * X - X * B‖ :=
    (sylvesterMap A B).continuous_of_finiteDimensional.norm
  obtain ⟨X, hX, hmin⟩ := (isCompact_sphere (0 : Matrix m n 𝕜) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr zero_le_one) hc.continuousOn
  rw [mem_sphere_zero_iff_norm] at hX
  refine ⟨X, hX, le_antisymm ?_ (sep_le_norm hX)⟩
  exact le_sep fun Y hY => hmin (mem_sphere_zero_iff_norm.mpr hY)

/-- If $X \neq 0$ and $A X - X B = c X$ for a scalar $c$, then $\operatorname{sep}(A, B) \le |c|$.
-/
theorem sep_le_norm_of_sylvesterMap_eq_smul {X : Matrix m n 𝕜} (hX : X ≠ 0) {c : 𝕜}
    (h : A * X - X * B = c • X) : sep A B ≤ ‖c‖ := by
  have := sep_mul_norm_le (A := A) (B := B) X
  rw [h, norm_smul] at this
  exact le_of_mul_le_mul_right this (norm_pos_iff.mpr hX)

/-- **Positivity of the separation.** Let $m, n \ge 1$. Then $\operatorname{sep}(A, B) > 0$ if and
only if the Sylvester operator $X \mapsto A X - X B$ is injective. -/
theorem sep_pos_iff [Nonempty m] [Nonempty n] :
    0 < sep A B ↔ Function.Injective (sylvesterMap A B) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  constructor
  · intro h X hX
    have := sep_mul_norm_le (A := A) (B := B) X
    rw [← sylvesterMap_apply, hX, norm_zero] at this
    exact norm_eq_zero.mp (le_antisymm (nonpos_of_mul_nonpos_right this h) (norm_nonneg _))
  · intro h
    obtain ⟨X, hX, hXeq⟩ := exists_sep_eq A B
    refine (sep_nonneg A B).lt_of_ne fun h0 => ?_
    rw [← h0, norm_eq_zero, ← sylvesterMap_apply] at hXeq
    simp [h X hXeq] at hX

/-- Let $A$ and $B$ be complex square matrices of orders $m, n \ge 1$. Then
$\operatorname{sep}(A, B) > 0$ if and only if the spectra of $A$ and $B$ are disjoint. This is
§7.2.4 of [golub2013matrix].

The field is an `RCLike` field that is algebraically closed, that is, $\mathbb{C}$. -/
theorem sep_pos_iff_disjoint_spectrum [IsAlgClosed 𝕜] [DecidableEq m] [DecidableEq n]
    [Nonempty m] [Nonempty n] : 0 < sep A B ↔ Disjoint (spectrum 𝕜 A) (spectrum 𝕜 B) := by
  rw [sep_pos_iff, ← sylvesterMap_bijective_iff_disjoint_spectrum]
  exact ⟨fun h => ⟨h, LinearMap.injective_iff_surjective.mp h⟩, fun h => h.1⟩

/-- **The separation bounds solutions** of the Sylvester equation. If
$\operatorname{sep}(A, B) > 0$, then for every $m \times n$ matrix $X$
$$\|X\|_F \le \frac{\|A X - X B\|_F}{\operatorname{sep}(A, B)}.$$
This is (7.3.20) of [golub2013matrix]. -/
theorem frobenius_norm_le_div_sep (h : 0 < sep A B) (X : Matrix m n 𝕜) :
    ‖X‖ ≤ ‖A * X - X * B‖ / sep A B := by
  rw [le_div_iff₀ h, mul_comm]
  exact sep_mul_norm_le X

/-- **The separation is at most the distance between eigenvalues.** If $\alpha$ is an eigenvalue of
$A$ and $\beta$ is an eigenvalue of $B$, then
$$\operatorname{sep}(A, B) \le |\alpha - \beta|.$$
This is P7.2.10 of [golub2013matrix].

The rank-one matrix $X = x y^T$, built from a right eigenvector $x$ of $A$ and a left
eigenvector $y$ of $B$, satisfies $A X - X B = (\alpha - \beta) X$. -/
theorem sep_le_norm_sub [DecidableEq m] [DecidableEq n] {α β : 𝕜} (hα : α ∈ spectrum 𝕜 A)
    (hβ : β ∈ spectrum 𝕜 B) : sep A B ≤ ‖α - β‖ := by
  obtain ⟨x, hx, hxA⟩ := (mem_spectrum_iff_exists_mulVec_eq_smul A α).mp hα
  obtain ⟨y, hy, hyB⟩ := exists_vecMul_eq_smul_of_mem_spectrum hβ
  refine sep_le_norm_of_sylvesterMap_eq_smul (X := vecMulVec x y) ?_
    (sylvesterMap_vecMulVec hxA hyB)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hy
  intro h0
  have := congrFun (congrFun h0 i) j
  rw [vecMulVec_apply, Matrix.zero_apply] at this
  exact mul_ne_zero hi hj this

/-- **Unitary invariance of the separation.** If $U$ and $V$ are unitary, then
$$\operatorname{sep}(U^H A U, V^H B V) = \operatorname{sep}(A, B).$$

The map $X \mapsto U X V^H$ is an isometry of the Frobenius unit sphere. -/
theorem sep_unitary_conj [DecidableEq m] [DecidableEq n] {U : Matrix m m 𝕜} {V : Matrix n n 𝕜}
    (hU : U ∈ unitaryGroup m 𝕜) (hV : V ∈ unitaryGroup n 𝕜) (A : Matrix m m 𝕜)
    (B : Matrix n n 𝕜) : sep (star U * A * U) (star V * B * V) = sep A B := by
  have hU' : U * star U = 1 := mem_unitaryGroup_iff.mp hU
  have hV' : V * star V = 1 := mem_unitaryGroup_iff.mp hV
  have hsU : star U ∈ unitaryGroup m 𝕜 := Unitary.star_mem hU
  have hsV : star V ∈ unitaryGroup n 𝕜 := Unitary.star_mem hV
  have hsU' : star U * U = 1 := mem_unitaryGroup_iff'.mp hU
  have hsV' : star V * V = 1 := mem_unitaryGroup_iff'.mp hV
  let e : {X : Matrix m n 𝕜 // ‖X‖ = 1} ≃ {X : Matrix m n 𝕜 // ‖X‖ = 1} :=
    { toFun := fun X => ⟨U * X.1 * star V, by
        rw [frobenius_norm_unitary_mul_mul_unitary hU _ hsV, X.2]⟩
      invFun := fun X => ⟨star U * X.1 * V, by
        rw [frobenius_norm_unitary_mul_mul_unitary hsU _ hV, X.2]⟩
      left_inv := fun X => Subtype.ext <| by
        simp only [← Matrix.mul_assoc, hsU', Matrix.one_mul]
        rw [Matrix.mul_assoc, hsV', Matrix.mul_one]
      right_inv := fun X => Subtype.ext <| by
        simp only [← Matrix.mul_assoc, hU', Matrix.one_mul]
        rw [Matrix.mul_assoc, hV', Matrix.mul_one] }
  refine Equiv.iInf_congr e fun X => ?_
  change ‖A * (U * X.1 * star V) - U * X.1 * star V * B‖ = _
  have : A * (U * X.1 * star V) - U * X.1 * star V * B =
      U * (star U * A * U * X.1 - X.1 * (star V * B * V)) * star V := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, hU', Matrix.one_mul]
    rw [Matrix.mul_assoc (U * X.1 * star V * B) V (star V), hV', Matrix.mul_one]
  rw [this, frobenius_norm_unitary_mul_mul_unitary hU _ hsV]

/-- **Perturbation of the separation.** For square matrices $A, E$ of order $m$ and $B, F$ of order
$n$,
$$\operatorname{sep}(A, B) - \|E\|_F - \|F\|_F \le \operatorname{sep}(A + E, B + F).$$
So the separation is 1-Lipschitz in each argument for the Frobenius norm. -/
theorem sep_sub_le_sep_add (A E : Matrix m m 𝕜) (B F : Matrix n n 𝕜) :
    sep A B - ‖E‖ - ‖F‖ ≤ sep (A + E) (B + F) := by
  rcases isEmpty_or_nonempty_index (m := m) (n := n) (𝕜 := 𝕜) with h | ⟨hm, hn⟩
  · rw [sep_of_isEmpty, sep_of_isEmpty]
    linarith [norm_nonneg E, norm_nonneg F]
  refine le_sep fun X hX => ?_
  have h1 := sep_le_norm (A := A) (B := B) hX
  have : A * X - X * B = ((A + E) * X - X * (B + F)) - E * X + X * F := by
    simp only [Matrix.add_mul, Matrix.mul_add]; abel
  rw [this] at h1
  have hEX := frobenius_norm_mul E X
  have hXF := frobenius_norm_mul X F
  rw [hX] at hEX hXF
  linarith [norm_add_le (((A + E) * X - X * (B + F)) - E * X) (X * F),
    norm_sub_le ((A + E) * X - X * (B + F)) (E * X)]

/-! ### Symmetry of the separation -/

/-- **The adjoint of the Sylvester operator** for the Frobenius inner product: for $m \times n$
matrices $X$ and $Y$,
$$\operatorname{tr}\bigl(Y^H (A X - X B)\bigr) = \operatorname{tr}\bigl((A^H Y - Y B^H)^H
  X\bigr).$$
-/
theorem trace_conjTranspose_mul_sylvesterMap (A : Matrix m m 𝕜) (B : Matrix n n 𝕜)
    (X Y : Matrix m n 𝕜) :
    trace (Yᴴ * (A * X - X * B)) = trace ((Aᴴ * Y - Y * Bᴴ)ᴴ * X) := by
  simp only [conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_sub,
    Matrix.sub_mul, trace_sub, Matrix.mul_assoc]
  rw [trace_mul_comm B, Matrix.mul_assoc]

/-- **A lower bound passes to the adjoint.** Let $c$ be real. If $c \|X\|_F \le \|A X - X B\|_F$ for
every $m \times n$ matrix $X$, then
$$c \|Y\|_F \le \|A^H Y - Y B^H\|_F$$
for every $m \times n$ matrix $Y$.

For $c > 0$ the Sylvester operator is injective, hence surjective. Write $Y = A X - X B$. Then
$\|Y\|_F^2 = \operatorname{Re} \operatorname{tr}\bigl((A^H Y - Y B^H)^H X\bigr) \le \|A^H Y - Y
B^H\|_F \|X\|_F$ and $\|X\|_F \le \|Y\|_F / c$. -/
theorem le_norm_sylvesterMap_conjTranspose_of_le {c : ℝ}
    (h : ∀ X : Matrix m n 𝕜, c * ‖X‖ ≤ ‖A * X - X * B‖) (Y : Matrix m n 𝕜) :
    c * ‖Y‖ ≤ ‖Aᴴ * Y - Y * Bᴴ‖ := by
  rcases le_or_gt c 0 with hc | hc
  · exact (mul_nonpos_of_nonpos_of_nonneg hc (norm_nonneg _)).trans (norm_nonneg _)
  have hinj : Function.Injective (sylvesterMap A B) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro X hX
    have := h X
    rw [← sylvesterMap_apply, hX, norm_zero] at this
    exact norm_eq_zero.mp (le_antisymm (nonpos_of_mul_nonpos_right this hc) (norm_nonneg _))
  obtain ⟨X, rfl⟩ := LinearMap.injective_iff_surjective.mp hinj Y
  rw [sylvesterMap_apply]
  set Y := A * X - X * B with hY
  have hsq : ‖Y‖ ^ 2 = RCLike.re (trace (Yᴴ * Y)) := by
    rw [← frobenius_norm_sq_eq_trace, RCLike.ofReal_re]
  have hcs : ‖Y‖ ^ 2 ≤ ‖Aᴴ * Y - Y * Bᴴ‖ * ‖X‖ := by
    rw [hsq]
    conv_lhs => rw [hY, trace_conjTranspose_mul_sylvesterMap, ← hY]
    exact re_trace_conjTranspose_mul_le _ _
  have hX := h X
  rw [← hY] at hX
  rcases (norm_nonneg Y).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]; exact norm_nonneg _
  have : c * ‖Y‖ ^ 2 ≤ ‖Aᴴ * Y - Y * Bᴴ‖ * ‖Y‖ := by
    calc c * ‖Y‖ ^ 2 ≤ c * (‖Aᴴ * Y - Y * Bᴴ‖ * ‖X‖) := by gcongr
      _ = ‖Aᴴ * Y - Y * Bᴴ‖ * (c * ‖X‖) := by ring
      _ ≤ ‖Aᴴ * Y - Y * Bᴴ‖ * ‖Y‖ := by gcongr
  nlinarith

/-- For an $m \times m$ matrix $A$ and an $n \times n$ matrix $B$,
$$\operatorname{sep}(A^H, B^H) = \operatorname{sep}(B, A).$$

The map $X \mapsto X^H$ maps the unit sphere of $m \times n$ matrices onto the unit sphere of
$n \times m$ matrices, and $A^H X^H - X^H B^H = -(B X - X A)^H$. -/
theorem sep_conjTranspose (A : Matrix m m 𝕜) (B : Matrix n n 𝕜) : sep Aᴴ Bᴴ = sep B A := by
  let e : {Z : Matrix n m 𝕜 // ‖Z‖ = 1} ≃ {X : Matrix m n 𝕜 // ‖X‖ = 1} :=
    { toFun := fun Z => ⟨Z.1ᴴ, by rw [frobenius_norm_conjTranspose, Z.2]⟩
      invFun := fun X => ⟨X.1ᴴ, by rw [frobenius_norm_conjTranspose, X.2]⟩
      left_inv := fun Z => Subtype.ext (conjTranspose_conjTranspose _)
      right_inv := fun X => Subtype.ext (conjTranspose_conjTranspose _) }
  refine (Equiv.iInf_congr e fun Z => ?_).symm
  change ‖Aᴴ * Z.1ᴴ - Z.1ᴴ * Bᴴ‖ = ‖B * Z.1 - Z.1 * A‖
  rw [← conjTranspose_mul, ← conjTranspose_mul, ← conjTranspose_sub,
    frobenius_norm_conjTranspose, norm_sub_rev]

private theorem sep_le_sep_conjTranspose (A : Matrix m m 𝕜) (B : Matrix n n 𝕜) :
    sep A B ≤ sep Aᴴ Bᴴ := by
  rcases isEmpty_or_nonempty_index (m := m) (n := n) (𝕜 := 𝕜) with h | ⟨hm, hn⟩
  · rw [sep_of_isEmpty, sep_of_isEmpty]
  refine le_sep fun Y hY => ?_
  have := le_norm_sylvesterMap_conjTranspose_of_le (A := A) (B := B) sep_mul_norm_le Y
  rwa [hY, mul_one] at this

/-- **The separation is symmetric:**
$$\operatorname{sep}(A, B) = \operatorname{sep}(B, A).$$

The perturbation theory of invariant subspaces bounds the inverse of the operator
$P \mapsto P A - B P$. By this result, the separation $\operatorname{sep}(A, B)$ of (7.2.5) of
[golub2013matrix] controls that operator, as the proof of Theorem 7.2.4 of [golub2013matrix]
uses. -/
theorem sep_comm (A : Matrix m m 𝕜) (B : Matrix n n 𝕜) : sep A B = sep B A :=
  le_antisymm ((sep_le_sep_conjTranspose A B).trans_eq (sep_conjTranspose A B))
    ((sep_le_sep_conjTranspose B A).trans_eq (sep_conjTranspose B A))

/-! ### Diagonal and Hermitian arguments -/

/-- Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, and let $a \in \mathbb{K}^m$ and
$b \in \mathbb{K}^n$ with $m, n \ge 1$. The separation of the diagonal matrices
$\operatorname{diag}(a)$ and $\operatorname{diag}(b)$ is the least distance between their
diagonal entries:
$$\operatorname{sep}(\operatorname{diag}(a), \operatorname{diag}(b)) = \min_{i, j} |a_i -
  b_j|.$$
-/
theorem sep_diagonal [DecidableEq m] [DecidableEq n] [Nonempty m] [Nonempty n] (a : m → 𝕜)
    (b : n → 𝕜) : sep (diagonal a) (diagonal b) = ⨅ i, ⨅ j, ‖a i - b j‖ := by
  have hbdd : ∀ i, BddBelow (Set.range fun j => ‖a i - b j‖) :=
    fun i => ⟨0, by rintro _ ⟨j, rfl⟩; exact norm_nonneg _⟩
  have hbdd' : BddBelow (Set.range fun i => ⨅ j, ‖a i - b j‖) :=
    ⟨0, by rintro _ ⟨i, rfl⟩; exact Real.iInf_nonneg fun _ => norm_nonneg _⟩
  set δ := ⨅ i, ⨅ j, ‖a i - b j‖ with hδ
  have hδle : ∀ i j, δ ≤ ‖a i - b j‖ := fun i j =>
    (ciInf_le hbdd' i).trans (ciInf_le (hbdd i) j)
  have hδ0 : 0 ≤ δ := Real.iInf_nonneg fun _ => Real.iInf_nonneg fun _ => norm_nonneg _
  refine le_antisymm ?_ (le_sep fun X hX => ?_)
  · obtain ⟨i⟩ := ‹Nonempty m›
    refine le_ciInf fun i => le_ciInf fun j => ?_
    refine sep_le_norm_of_sylvesterMap_eq_smul (X := single i j 1) ?_ ?_
    · intro h0
      simpa using congrFun (congrFun h0 i) j
    · ext k l
      rw [← sylvesterMap_apply, sylvesterMap_diagonal_apply, Matrix.smul_apply, single_apply,
        smul_eq_mul]
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h
        ring
      · simp
  · have hsq : δ ^ 2 ≤ ‖diagonal a * X - X * diagonal b‖ ^ 2 := by
      rw [frobenius_norm_sq_eq_sum_sq]
      calc δ ^ 2 = δ ^ 2 * ‖X‖ ^ 2 := by rw [hX, one_pow, mul_one]
        _ = ∑ i, ∑ j, δ ^ 2 * ‖X i j‖ ^ 2 := by
          rw [frobenius_norm_sq_eq_sum_sq, Finset.mul_sum]
          simp only [Finset.mul_sum]
        _ ≤ _ := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          rw [← sylvesterMap_apply, sylvesterMap_diagonal_apply, norm_mul, mul_pow]
          gcongr
          exact hδle i j
    exact (pow_le_pow_iff_left₀ hδ0 (norm_nonneg _) two_ne_zero).mp hsq

/-- **The separation of two Hermitian matrices is the distance between their spectra.** Let $A$ and
$B$ be Hermitian of orders $m, n \ge 1$, with eigenvalues $\lambda_i(A)$ and $\lambda_j(B)$.
Then
$$\operatorname{sep}(A, B) = \min_{i, j} |\lambda_i(A) - \lambda_j(B)|.$$
This is P8.1.9 of [golub2013matrix], the step used in Theorem 8.1.10.

The eigenvalues are `Matrix.IsHermitian.eigenvalues`. Both matrices are unitarily diagonalizable
by `Matrix.IsHermitian.star_eigenvectorUnitary_mul_mul`, the separation is unitarily invariant,
and `Matrix.sep_diagonal` computes it for diagonal matrices. -/
theorem IsHermitian.sep_eq_iInf_abs_eigenvalues_sub [DecidableEq m] [DecidableEq n]
    [Nonempty m] [Nonempty n] (hA : A.IsHermitian) (hB : B.IsHermitian) :
    sep A B = ⨅ i, ⨅ j, |hA.eigenvalues i - hB.eigenvalues j| := by
  rw [← sep_unitary_conj hA.eigenvectorUnitary.2 hB.eigenvectorUnitary.2,
    hA.star_eigenvectorUnitary_mul_mul, hB.star_eigenvectorUnitary_mul_mul, sep_diagonal]
  simp only [Function.comp_apply, ← RCLike.ofReal_sub, RCLike.norm_ofReal]

/-- **The separation from a scalar is a least singular value.** Let $c$ be a scalar and $T$ a square
matrix of order $n$. Then
$$\operatorname{sep}([c], T) = \sigma_{\min}(T - c I),$$
where $[c]$ is the $1 \times 1$ matrix with the entry $c$. This is a step of the proof of
Corollary 7.2.6 of [golub2013matrix].

The least singular value is `⨅ i, (T - c • 1).colSingularValues i`, the infimum of the singular
values indexed by the columns. It is $0$ when $n = 0$. By `Matrix.sep_comm` the unknown is a
column $x$. On a column the Sylvester operator is $x \mapsto (T - c I) x$ and the Frobenius norm
is the Euclidean norm, so the least stretch is $\sigma_{\min}$ by
`Matrix.iInf_colSingularValues_eq_iInf_norm`. -/
theorem sep_eq_iInf_colSingularValues [DecidableEq n] (c : 𝕜) (T : Matrix n n 𝕜) :
    sep (of fun _ _ => c : Matrix Unit Unit 𝕜) T = ⨅ i, (T - c • 1).colSingularValues i := by
  rw [sep_comm, iInf_colSingularValues_eq_iInf_norm, sep]
  let e : EuclideanSpace 𝕜 n ≃ Matrix n Unit 𝕜 :=
    { toFun := fun x => replicateCol Unit (WithLp.ofLp x)
      invFun := fun X => WithLp.toLp 2 fun i => X i ()
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hnorm : ∀ x, ‖e x‖ = ‖x‖ := fun x => frobenius_norm_replicateCol _
  let e' : {x : EuclideanSpace 𝕜 n // ‖x‖ = 1} ≃ {X : Matrix n Unit 𝕜 // ‖X‖ = 1} :=
    e.subtypeEquiv fun x => by rw [hnorm]
  conv_lhs => rw [← e'.iInf_comp]
  refine congrArg _ (funext fun x => ?_)
  have hv : T * replicateCol Unit (WithLp.ofLp (x : EuclideanSpace 𝕜 n)) -
      replicateCol Unit (WithLp.ofLp (x : EuclideanSpace 𝕜 n)) * of (fun _ _ => c) =
        replicateCol Unit ((T - c • 1) *ᵥ WithLp.ofLp (x : EuclideanSpace 𝕜 n)) := by
    ext i j
    simp only [sub_mulVec, smul_mulVec, one_mulVec]
    simp [Matrix.mul_apply, mulVec, dotProduct, mul_comm]
  change ‖T * replicateCol Unit (WithLp.ofLp (x : EuclideanSpace 𝕜 n)) -
      replicateCol Unit (WithLp.ofLp (x : EuclideanSpace 𝕜 n)) * of (fun _ _ => c)‖ = _
  rw [hv, frobenius_norm_replicateCol]
  rfl

end Sep

end Matrix
