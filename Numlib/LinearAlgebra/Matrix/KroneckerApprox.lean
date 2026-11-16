/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Matrix.SingularValues
import Numlib.Eigen.Normal
import Numlib.LinearAlgebra.Matrix.HermitianPart
import Numlib.LinearAlgebra.Matrix.Kronecker
import Numlib.LinearAlgebra.Matrix.Rank

/-!
# Approximation by Kronecker products

The Van Loan–Pitsianis rearrangement $\mathcal{R}$ ([golub2013matrix], §12.3.6–12.3.9, after Van
Loan and Pitsianis, 1993) turns Kronecker products into rank-one matrices:
$$\mathcal{R}(B \otimes C) = \operatorname{vec} B \, (\operatorname{vec} C)^T.$$
It permutes the entries, so it is an isometry for the Frobenius norm. Hence every statement about
the nearest Kronecker product, or the nearest sum of $r$ Kronecker products, is a statement about
the nearest matrix of low rank to $\mathcal{R}(A)$. This file defines $\mathcal{R}$ and the
Kronecker product rank, proves the Kronecker product SVD and the nearest sum of $r$ Kronecker
products, and proves the two structured nearest-rank lemmas of [golub2013matrix], §12.3.8: the
nearest symmetric matrix of rank at most one (Lemma 12.3.2) and the nearest skew-symmetric matrix of
rank at most two (Lemma 12.3.3).

## Main definitions

* `Matrix.kroneckerRearrange`, `Matrix.kroneckerRearrangeLinearEquiv`: the rearrangement
  $\mathcal{R}$, as a map and as a linear equivalence.
* `Matrix.kroneckerRank`: the Kronecker product rank, the rank of $\mathcal{R}(A)$.

## Main results

* `Matrix.kroneckerRearrange_kronecker`: $\mathcal{R}(B \otimes C) = \operatorname{vec} B \,
  (\operatorname{vec} C)^T$.
* `Matrix.frobenius_norm_kroneckerRearrange`: $\|\mathcal{R}(A)\|_F = \|A\|_F$.
* `Matrix.eq_sum_kronecker_iff`: $A$ is a sum of Kronecker products if and only if $\mathcal{R}(A)$
  is the corresponding sum of rank-one matrices.
* `Matrix.kroneckerRank_le_iff`: the Kronecker product rank is the least number of Kronecker
  products whose sum is $A$.
* `Matrix.exists_kroneckerSVD`: the Kronecker product SVD, Theorem 12.3.1 of [golub2013matrix].
* `Matrix.isLeast_frobenius_norm_sub_sum_kronecker`: the Frobenius distance from $A$ to the sums of
  $r$ Kronecker products, (12.3.14)–(12.3.19) of [golub2013matrix].
* `Matrix.isMinOn_frobenius_norm_sub_symm_rank_le_one`: Lemma 12.3.2 of [golub2013matrix].
* `Matrix.exists_eq_vecMulVec_sub_vecMulVec_of_rank_le_two`: a skew-symmetric matrix of rank at most
  two is $x y^T - y x^T$.
* `Matrix.isMinOn_frobenius_norm_sub_skew_rank_le_two`: Lemma 12.3.3 of [golub2013matrix].

## Proof outline

The two lemmas of §12.3.8 rest on the norm identities `Matrix.norm_sub_smul_vecMulVec_self_sq` and
`Matrix.norm_sub_skew_sq`, which express the Frobenius distance from $M$ to $\alpha x x^T$ and to
$x y^T - y x^T$.

## Implementation notes

* The indices are typed. For $A$ indexed by $(m_1 \times m_2) \times (n_1 \times n_2)$, the
  rearrangement $\mathcal{R}(A)$ is indexed by $(n_1 \times m_1) \times (n_2 \times m_2)$, and its
  entry at $((j, i), (l, k))$ is $A_{(i,k),(j,l)}$. The row $(j, i)$ is the block $A_{ij}$, in the
  column-major block order of the book. The column $(l, k)$ indexes $\operatorname{vec} A_{ij}$,
  since Mathlib's `Matrix.vec` is column-major, $(\operatorname{vec} X)_{(l,k)} = X_{kl}$.
* Lemmas 12.3.2 and 12.3.3 are stated with the conditions $\operatorname{rank} Z \le 1$ and
  $\operatorname{rank} Z \le 2$. The book's conditions $\operatorname{rank} Z = 1$ and
  $\operatorname{rank} Z = 2$ fail when the symmetric or skew-symmetric part of $M$ is zero, because
  then the infimum over the matrices of exact rank is not attained.
-/

open scoped Kronecker Matrix

namespace Matrix

variable {R : Type*} {m₁ m₂ n₁ n₂ : Type*}

/-! ### The rearrangement -/

/-- The **Van Loan–Pitsianis rearrangement** $\mathcal{R}(A)$ of a matrix $A$ indexed by
$(m_1 \times m_2) \times (n_1 \times n_2)$: the matrix indexed by
$(n_1 \times m_1) \times (n_2 \times m_2)$ whose row $(j, i)$ is
$(\operatorname{vec} A_{ij})^T$, for the block $A_{ij} = (A_{(i,k),(j,l)})_{k,l}$. Its entry at
$((j, i), (l, k))$ is $A_{(i,k),(j,l)}$.

This is the rearrangement of [golub2013matrix], §12.3.6, (12.3.16) and the display after it. -/
def kroneckerRearrange (A : Matrix (m₁ × m₂) (n₁ × n₂) R) : Matrix (n₁ × m₁) (n₂ × m₂) R :=
  of fun ji lk => A (ji.2, lk.2) (ji.1, lk.1)

/-- The entry of $\mathcal{R}(A)$ at $((j, i), (l, k))$ is $A_{(i,k),(j,l)}$. -/
@[simp]
theorem kroneckerRearrange_apply (A : Matrix (m₁ × m₂) (n₁ × n₂) R) (i : m₁) (j : n₁) (k : m₂)
    (l : n₂) : kroneckerRearrange A (j, i) (l, k) = A (i, k) (j, l) :=
  rfl

/-- The rearrangement $\mathcal{R}$ as a linear equivalence. -/
def kroneckerRearrangeLinearEquiv [Semiring R] :
    Matrix (m₁ × m₂) (n₁ × n₂) R ≃ₗ[R] Matrix (n₁ × m₁) (n₂ × m₂) R where
  toFun := kroneckerRearrange
  invFun B := of fun ik jl => B (jl.1, ik.1) (jl.2, ik.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The linear equivalence `Matrix.kroneckerRearrangeLinearEquiv` maps $A$ to $\mathcal{R}(A)$. -/
@[simp]
theorem kroneckerRearrangeLinearEquiv_apply [Semiring R] (A : Matrix (m₁ × m₂) (n₁ × n₂) R) :
    kroneckerRearrangeLinearEquiv A = kroneckerRearrange A :=
  rfl

/-- For matrices $B$ indexed by $m_1 \times n_1$ and $C$ indexed by $m_2 \times n_2$, the
rearrangement of the Kronecker product is a rank-one matrix:
$$\mathcal{R}(B \otimes C) = \operatorname{vec} B \, (\operatorname{vec} C)^T.$$

This is stated in [golub2013matrix], §12.3.6. -/
theorem kroneckerRearrange_kronecker [Mul R] (B : Matrix m₁ n₁ R) (C : Matrix m₂ n₂ R) :
    kroneckerRearrange (B ⊗ₖ C) = vecMulVec (vec B) (vec C) := by
  ext ⟨j, i⟩ ⟨l, k⟩
  rfl

/-- Over a commutative semiring, let $A$ be indexed by $(m_1 \times m_2) \times (n_1 \times n_2)$,
let $\tau$ be a finite type, and let $\sigma_k$ be scalars and $u_k$, $v_k$ vectors indexed by
$n_1 \times m_1$ and $n_2 \times m_2$, for $k \in \tau$. Then
$$A = \sum_k \sigma_k \, \operatorname{unvec}(u_k) \otimes \operatorname{unvec}(v_k) \iff
  \mathcal{R}(A) = \sum_k \sigma_k \, u_k v_k^T.$$

This is the argument of the proof of Theorem 12.3.1 of [golub2013matrix]. Here
$\operatorname{unvec}$ is `Matrix.unvec`, the inverse of the column stacking. -/
theorem eq_sum_kronecker_iff [CommSemiring R] {τ : Type*} [Fintype τ]
    (A : Matrix (m₁ × m₂) (n₁ × n₂) R) (σ : τ → R) (u : τ → n₁ × m₁ → R) (v : τ → n₂ × m₂ → R) :
    A = ∑ k, σ k • (unvec (u k) ⊗ₖ unvec (v k))
      ↔ kroneckerRearrange A = ∑ k, σ k • vecMulVec (u k) (v k) := by
  have h : kroneckerRearrangeLinearEquiv (∑ k, σ k • (unvec (u k) ⊗ₖ unvec (v k)))
      = ∑ k, σ k • vecMulVec (u k) (v k) := by
    simp only [map_sum, map_smul, kroneckerRearrangeLinearEquiv_apply,
      kroneckerRearrange_kronecker, vec_unvec]
  rw [← h, ← kroneckerRearrangeLinearEquiv_apply, kroneckerRearrangeLinearEquiv.injective.eq_iff]

/-- The **Kronecker product rank** of a matrix $A$ indexed by
$(m_1 \times m_2) \times (n_1 \times n_2)$: the rank of the rearrangement $\mathcal{R}(A)$.

This is the definition of [golub2013matrix], §12.3.6. -/
noncomputable def kroneckerRank [CommRing R] [Fintype n₂] [Fintype m₂]
    (A : Matrix (m₁ × m₂) (n₁ × n₂) R) : ℕ :=
  (kroneckerRearrange A).rank

/-- Over a commutative semiring, the rearrangement of a sum $\sum_k B_k \otimes C_k$ is the product
$PQ$, where the column $k$ of $P$ is $\operatorname{vec} B_k$ and the row $k$ of $Q$ is
$(\operatorname{vec} C_k)^T$. -/
theorem kroneckerRearrange_sum_kronecker [CommSemiring R] {r : Type*} [Fintype r]
    (B : r → Matrix m₁ n₁ R) (C : r → Matrix m₂ n₂ R) :
    kroneckerRearrange (∑ k, B k ⊗ₖ C k)
      = (of fun x k => vec (B k) x : Matrix (n₁ × m₁) r R) * of fun k y => vec (C k) y := by
  rw [← kroneckerRearrangeLinearEquiv_apply, map_sum]
  ext x y
  simp only [kroneckerRearrangeLinearEquiv_apply, kroneckerRearrange_kronecker, Matrix.sum_apply,
    vecMulVec_apply, Matrix.mul_apply, of_apply]

/-- **The Kronecker product rank counts Kronecker products.** Let $K$ be a field, let $A$ be a
matrix over $K$ indexed by $(m_1 \times m_2) \times (n_1 \times n_2)$, and let
$r \in \mathbb{N}$. Then the Kronecker product rank of $A$ is at most $r$ if and only if there
are matrices $B_0, \dots, B_{r-1}$ indexed by $m_1 \times n_1$ and $C_0, \dots, C_{r-1}$ indexed
by $m_2 \times n_2$ with
$$A = \sum_{k < r} B_k \otimes C_k.$$

This is stated in [golub2013matrix], §12.3.6. The proof reads the rank factorization of
$\mathcal{R}(A)$ (`Matrix.rank_le_iff_exists_mul`) through
`Matrix.kroneckerRearrange_sum_kronecker`. -/
theorem kroneckerRank_le_iff {K : Type*} [Field K] [Fintype m₂] [Fintype n₂]
    (A : Matrix (m₁ × m₂) (n₁ × n₂) K) (r : ℕ) :
    kroneckerRank A ≤ r ↔ ∃ (B : Fin r → Matrix m₁ n₁ K) (C : Fin r → Matrix m₂ n₂ K),
      A = ∑ k, B k ⊗ₖ C k := by
  rw [kroneckerRank, rank_le_iff_exists_mul]
  constructor
  · rintro ⟨P, Q, hPQ⟩
    refine ⟨fun k => unvec fun x => P x k, fun k => unvec (Q k), ?_⟩
    apply kroneckerRearrangeLinearEquiv.injective
    rw [kroneckerRearrangeLinearEquiv_apply, kroneckerRearrangeLinearEquiv_apply,
      kroneckerRearrange_sum_kronecker, hPQ]
    rfl
  · rintro ⟨B, C, rfl⟩
    exact ⟨_, _, kroneckerRearrange_sum_kronecker B C⟩

/-! ### The rearrangement is a Frobenius isometry -/

section Norm

open scoped Matrix.Norms.Frobenius

variable {𝕜 : Type*} [RCLike 𝕜] [Fintype m₁] [Fintype m₂] [Fintype n₁] [Fintype n₂]

/-- Let $A$ be a matrix over $\mathbb{R}$ or $\mathbb{C}$ indexed by
$(m_1 \times m_2) \times (n_1 \times n_2)$. Then the rearrangement has the same Frobenius norm:
$$\|\mathcal{R}(A)\|_F = \|A\|_F.$$

This is stated in [golub2013matrix], §12.3.6, in the display after (12.3.14). The rearrangement
permutes the entries. -/
theorem frobenius_norm_kroneckerRearrange (A : Matrix (m₁ × m₂) (n₁ × n₂) 𝕜) :
    ‖kroneckerRearrange A‖ = ‖A‖ := by
  refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [frobenius_norm_sq_eq_sum_sq, frobenius_norm_sq_eq_sum_sq, ← Fintype.sum_prod_type',
    ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv ((Equiv.prodProdProdComm n₁ m₁ n₂ m₂).trans (Equiv.prodComm _ _)) _ _
    fun _ => rfl

end Norm

/-! ### The Kronecker product SVD -/

section KroneckerSVD

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **The Kronecker product SVD.** Let $A$ be a matrix over $\mathbb{K} = \mathbb{R}$ or
$\mathbb{C}$ indexed by $(m_1 \times m_2) \times (n_1 \times n_2)$, and let $r$ be its Kronecker
product rank. Let $\sigma_0 \ge \sigma_1 \ge \dots$ be the singular values of $\mathcal{R}(A)$
in decreasing order. Then $\sigma_k > 0$ for $k < r$, and there are matrices
$U_0, \dots, U_{r-1}$ indexed by $m_1 \times n_1$ and $V_0, \dots, V_{r-1}$ indexed by
$m_2 \times n_2$ such that the vectors $\operatorname{vec} U_k$ are orthonormal, the vectors
$\operatorname{vec} V_k$ are orthonormal, and
$$A = \sum_{k < r} \sigma_k \, U_k \otimes V_k.$$

This is Theorem 12.3.1 of [golub2013matrix]. The proof pulls back the singular value expansion
of $\mathcal{R}(A)$ with `Matrix.eq_sum_kronecker_iff`. The singular values are
`Matrix.sortedSingularValues`, indexed from $0$. Orthonormality of the $\operatorname{vec} U_k$
is orthonormality for the Frobenius inner product. -/
theorem exists_kroneckerSVD [Fintype m₂] [Fintype n₁] [Fintype n₂] [Fintype m₁] [DecidableEq n₂]
    [DecidableEq m₂] (A : Matrix (m₁ × m₂) (n₁ × n₂) 𝕜) :
    ∃ (U : Fin (kroneckerRank A) → Matrix m₁ n₁ 𝕜) (V : Fin (kroneckerRank A) → Matrix m₂ n₂ 𝕜),
      Orthonormal 𝕜 (fun k => WithLp.toLp 2 (vec (U k))) ∧
      Orthonormal 𝕜 (fun k => WithLp.toLp 2 (vec (V k))) ∧
      (∀ k : Fin (kroneckerRank A), 0 < (kroneckerRearrange A).sortedSingularValues k) ∧
      A = ∑ k : Fin (kroneckerRank A),
        (((kroneckerRearrange A).sortedSingularValues k : ℝ) : 𝕜) • (U k ⊗ₖ V k) := by
  obtain ⟨u, v, hu, hv, hpos, h⟩ :=
    exists_eq_sum_sortedSingularValues_smul_vecMulVec (kroneckerRearrange A)
  refine ⟨fun k => unvec ⇑(u k), fun k => unvec (star ⇑(v k)), hu, orthonormal_toLp_star hv,
    hpos, ?_⟩
  exact (eq_sum_kronecker_iff A
    (fun k : Fin (kroneckerRank A) => (((kroneckerRearrange A).sortedSingularValues k : ℝ) : 𝕜))
    (fun k => ⇑(u k)) (fun k => star ⇑(v k))).2 h

end KroneckerSVD

/-! ### The nearest sum of Kronecker products -/

section Nearest

variable {𝕜 : Type*} [RCLike 𝕜] [Fintype m₁] [Fintype m₂] [Fintype n₁] [Fintype n₂]
  [DecidableEq m₂] [DecidableEq n₂]

open scoped Matrix.Norms.Frobenius in
/-- **The nearest sum of $r$ Kronecker products.** Let $A$ be a matrix over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$ indexed by $(m_1 \times m_2) \times (n_1 \times n_2)$,
and let $r \in \mathbb{N}$. Let $\sigma_0 \ge \sigma_1 \ge \dots$ be the singular values of
$\mathcal{R}(A)$ in decreasing order, and let $N = \min(|n_1| |m_1|, |n_2| |m_2|)$. Then the
least value of $\|A - X\|_F$ over the matrices $X$ of Kronecker product rank at most $r$ exists
and is
$$\Big(\sum_{r \le i < N} \sigma_i^2\Big)^{1/2}.$$

This is (12.3.14)–(12.3.15), the nearest Kronecker product problem for $r = 1$, and (12.3.19) of
[golub2013matrix]. The matrices of Kronecker product rank at most $r$ are the sums of $r$
Kronecker products (`Matrix.kroneckerRank_le_iff`). The singular values are indexed from $0$,
and the sum is empty, with value $0$, for $r \ge N$. The rearrangement is a linear Frobenius
isometry (`Matrix.frobenius_norm_kroneckerRearrange`) that carries the Kronecker product rank to
the rank, so this is the Eckart–Young–Mirsky theorem
`Matrix.isLeast_frobenius_norm_sub_of_rank_le` for $\mathcal{R}(A)$. The minimum is attained at
the truncated Kronecker product SVD. -/
theorem isLeast_frobenius_norm_sub_sum_kronecker (A : Matrix (m₁ × m₂) (n₁ × n₂) 𝕜) (r : ℕ) :
    IsLeast ((fun X => ‖A - X‖) '' {X | kroneckerRank X ≤ r})
      √(∑ i ∈ Finset.Ico r (min (Fintype.card (n₁ × m₁)) (Fintype.card (n₂ × m₂))),
        (kroneckerRearrange A).sortedSingularValues i ^ 2) := by
  have himage : (fun X => ‖A - X‖) '' {X | kroneckerRank X ≤ r} =
      (fun Y => ‖kroneckerRearrange A - Y‖) '' {Y | Y.rank ≤ r} := by
    ext t
    constructor
    · rintro ⟨X, hX, rfl⟩
      refine ⟨kroneckerRearrange X, hX, ?_⟩
      change ‖kroneckerRearrange A - kroneckerRearrange X‖ = ‖A - X‖
      rw [← frobenius_norm_kroneckerRearrange (A - X)]
      rfl
    · rintro ⟨Y, hY, rfl⟩
      refine ⟨kroneckerRearrangeLinearEquiv.symm Y, ?_, ?_⟩
      · change (kroneckerRearrange (kroneckerRearrangeLinearEquiv.symm Y)).rank ≤ r
        rwa [← kroneckerRearrangeLinearEquiv_apply, LinearEquiv.apply_symm_apply]
      · dsimp only
        rw [← frobenius_norm_kroneckerRearrange, ← kroneckerRearrangeLinearEquiv_apply, map_sub,
          LinearEquiv.apply_symm_apply, kroneckerRearrangeLinearEquiv_apply]
  rw [himage]
  exact isLeast_frobenius_norm_sub_of_rank_le _ r

end Nearest

/-! ### The norm identities behind Lemmas 12.3.2 and 12.3.3 -/

section Identities

open scoped Matrix.Norms.Frobenius

variable {n : Type*} [Fintype n]

/-- The squared Frobenius norm of a real matrix is the sum of the squares of its entries. -/
private theorem frobenius_norm_sq_real {p q : Type*} [Fintype p] [Fintype q] (A : Matrix p q ℝ) :
    ‖A‖ ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  rw [frobenius_norm_sq_eq_sum_sq]
  simp only [Real.norm_eq_abs, sq_abs]

/-- Let $M$ be a real square matrix, $x$ a real vector with $x^T x = 1$, and
$\alpha \in \mathbb{R}$. Then
$$\|M - \alpha x x^T\|_F^2 = \|M\|_F^2 - 2 \alpha \, x^T M x + \alpha^2.$$

This is the identity behind Lemma 12.3.2 of [golub2013matrix] (Problem P12.3.11). The book
writes $x^T T x$ with $T = (M + M^T)/2$, which is the same number. -/
theorem norm_sub_smul_vecMulVec_self_sq (M : Matrix n n ℝ) {x : n → ℝ} (hx : x ⬝ᵥ x = 1)
    (α : ℝ) : ‖M - α • vecMulVec x x‖ ^ 2 = ‖M‖ ^ 2 - 2 * α * (x ⬝ᵥ (M *ᵥ x)) + α ^ 2 := by
  have hxx : (∑ i, ∑ j, x i ^ 2 * x j ^ 2) = 1 := by
    rw [← Finset.sum_mul_sum, ← sq]
    simp only [dotProduct, ← sq] at hx
    rw [hx, one_pow]
  have hM : x ⬝ᵥ (M *ᵥ x) = ∑ i, ∑ j, x i * M i j * x j := by
    simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  rw [frobenius_norm_sq_real, frobenius_norm_sq_real, hM]
  conv_rhs => rw [← mul_one (α ^ 2), ← hxx]
  simp only [Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Let $M$ be a real square matrix and $x, y$ real vectors. Then
$$\|M - (x y^T - y x^T)\|_F^2 = \|M\|_F^2 + 2 \|x\|^2 \|y\|^2 - 2 (x^T y)^2 - 2 (x^T M y - y^T M
  x).$$

This is the identity behind Lemma 12.3.3 of [golub2013matrix] (Problem P12.3.12). The book
writes the last term as $4 x^T S y$ with $S = (M - M^T)/2$, which is the same number. -/
theorem norm_sub_skew_sq (M : Matrix n n ℝ) (x y : n → ℝ) :
    ‖M - (vecMulVec x y - vecMulVec y x)‖ ^ 2
      = ‖M‖ ^ 2 + 2 * ((x ⬝ᵥ x) * (y ⬝ᵥ y)) - 2 * (x ⬝ᵥ y) ^ 2
        - 2 * (x ⬝ᵥ (M *ᵥ y) - y ⬝ᵥ (M *ᵥ x)) := by
  have h1 : 2 * ((x ⬝ᵥ x) * (y ⬝ᵥ y)) = ∑ i, ∑ j, (x i ^ 2 * y j ^ 2 + y i ^ 2 * x j ^ 2) := by
    have ha : (x ⬝ᵥ x) * (y ⬝ᵥ y) = ∑ i, ∑ j, x i ^ 2 * y j ^ 2 := by
      simp only [dotProduct, Finset.sum_mul_sum, sq]
    have hb : (x ⬝ᵥ x) * (y ⬝ᵥ y) = ∑ i, ∑ j, y i ^ 2 * x j ^ 2 := by
      rw [mul_comm]
      simp only [dotProduct, Finset.sum_mul_sum, sq]
    simp only [Finset.sum_add_distrib]
    rw [← ha, ← hb]
    ring
  have h2 : (x ⬝ᵥ y) ^ 2 = ∑ i, ∑ j, x i * y i * (x j * y j) := by
    simp only [dotProduct, sq, Finset.sum_mul_sum]
  have h3 : x ⬝ᵥ (M *ᵥ y) = ∑ i, ∑ j, x i * M i j * y j := by
    simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  have h4 : y ⬝ᵥ (M *ᵥ x) = ∑ i, ∑ j, x j * M i j * y i := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [frobenius_norm_sq_real, frobenius_norm_sq_real, h1, h2, h3, h4]
  simp only [Matrix.sub_apply, vecMulVec_apply, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Identities

/-! ### Lemma 12.3.2: the nearest symmetric matrix of rank at most one -/

section Lemma1232

open scoped Matrix.Norms.Frobenius InnerProductSpace

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Let $M$ be a real square matrix, let $T = (M + M^T)/2$, and let $\alpha_k$ be an eigenvalue of
$T$ of largest modulus, $|\alpha_i| \le |\alpha_k|$ for all $i$, with unit eigenvector $q_k$.
Then $\alpha_k q_k q_k^T$ minimizes $\|M - Z\|_F$ over the real symmetric matrices $Z$ with
$\operatorname{rank} Z \le 1$. This is Lemma 12.3.2 of [golub2013matrix].

The book states the lemma for $\operatorname{rank} Z = 1$. This fails when $T = 0$, because then
the infimum over the matrices of rank exactly one is not attained; the condition
$\operatorname{rank} Z \le 1$ is the correct reading. The matrix $T$ is
`Matrix.hermitianPart M`, and its eigenvalues and eigenvectors are
`Matrix.IsHermitian.eigenvalues` and `Matrix.IsHermitian.eigenvectorBasis`. -/
theorem isMinOn_frobenius_norm_sub_symm_rank_le_one (M : Matrix n n ℝ) {k : n}
    (hk : ∀ i, |(hermitianPart_isHermitian M).eigenvalues i|
      ≤ |(hermitianPart_isHermitian M).eigenvalues k|) :
    IsMinOn (fun Z => ‖M - Z‖) {Z | Z.IsSymm ∧ Z.rank ≤ 1}
      ((hermitianPart_isHermitian M).eigenvalues k
        • vecMulVec ⇑((hermitianPart_isHermitian M).eigenvectorBasis k)
          ⇑((hermitianPart_isHermitian M).eigenvectorBasis k)) := by
  set hT := hermitianPart_isHermitian M
  set α := hT.eigenvalues k
  set q := ⇑(hT.eigenvectorBasis k)
  have hq : q ⬝ᵥ q = 1 := by
    simpa only [star_trivial] using hT.star_dotProduct_eigenvectorBasis_self k
  have hqM : q ⬝ᵥ (M *ᵥ q) = α := by
    rw [← dotProduct_mulVec_hermitianPart, hT.mulVec_eigenvectorBasis, dotProduct_smul, hq,
      smul_eq_mul, mul_one]
  have hopt : ‖M - α • vecMulVec q q‖ ^ 2 = ‖M‖ ^ 2 - α ^ 2 := by
    rw [norm_sub_smul_vecMulVec_self_sq M hq, hqM]
    ring
  rintro Z ⟨hZs, hZr⟩
  rcases isEmpty_or_nonempty n with hn | hn
  · change ‖M - α • vecMulVec q q‖ ≤ ‖M - Z‖
    rw [Subsingleton.elim Z (α • vecMulVec q q)]
  obtain ⟨β, x, hx, rfl⟩ := exists_eq_smul_vecMulVec_self_of_rank_le_one hZs hZr
  have ht : |x ⬝ᵥ (M *ᵥ x)| ≤ |α| := by
    rw [← dotProduct_mulVec_hermitianPart]
    exact abs_dotProduct_mulVec_le hT hk hx
  have ht2 := sq_le_sq.2 ht
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  change ‖M - α • vecMulVec q q‖ ^ 2 ≤ ‖M - β • vecMulVec x x‖ ^ 2
  rw [hopt, norm_sub_smul_vecMulVec_self_sq M hx]
  nlinarith [sq_nonneg (β - x ⬝ᵥ (M *ᵥ x))]

end Lemma1232

/-! ### Lemma 12.3.3: the nearest skew-symmetric matrix of rank at most two -/

section Lemma1233

open scoped Matrix.Norms.Frobenius

variable {n : Type*} [Fintype n]

/-- **The normal form of a skew-symmetric matrix of rank at most two.** Let $K$ be a field with
$2 \ne 0$, and let $Z$ be a square matrix over $K$ with $Z^T = -Z$ and
$\operatorname{rank} Z \le 2$. Then there are vectors $x, y$ with
$$Z = x y^T - y x^T.$$

If $c = z_{ij} \ne 0$, the $3 \times 3$ minors on the rows $i, j, l$ and the columns $i, j, k$
vanish. This gives $c Z = z_i z_j^T - z_j z_i^T$ for the columns $z_i, z_j$ of $Z$. -/
theorem exists_eq_vecMulVec_sub_vecMulVec_of_rank_le_two {K : Type*} [Field K] [NeZero (2 : K)]
    {Z : Matrix n n K} (hZ : Zᵀ = -Z) (hr : Z.rank ≤ 2) :
    ∃ x y : n → K, Z = vecMulVec x y - vecMulVec y x := by
  have hs : ∀ i j, Z i j = -Z j i := fun i j => by
    simpa using congrFun (congrFun hZ j) i
  have hd : ∀ i, Z i i = 0 := fun i => by
    have h2 : (2 : K) * Z i i = 0 := by linear_combination hs i i
    exact (mul_eq_zero.1 h2).resolve_left two_ne_zero
  by_cases h0 : ∀ i j, Z i j = 0
  · exact ⟨0, 0, by ext i j; simp [h0]⟩
  push Not at h0
  obtain ⟨i, j, hij⟩ := h0
  have key : ∀ l k, Z i j * Z l k = Z i k * Z l j - Z j k * Z l i := by
    intro l k
    by_contra hne
    have hdet : (Z.submatrix ![i, j, l] ![i, j, k]).det ≠ 0 := by
      have e : (Z.submatrix ![i, j, l] ![i, j, k]).det
          = Z i j * (Z i j * Z l k - (Z i k * Z l j - Z j k * Z l i)) := by
        rw [det_fin_three]
        simp only [submatrix_apply, cons_val_zero, cons_val_one, cons_val_two, head_cons, tail_cons,
          hd]
        rw [hs j i]
        ring
      rw [e]
      exact mul_ne_zero hij (sub_ne_zero.2 hne)
    have := card_le_rank_of_det_submatrix_ne_zero Z hdet
    omega
  refine ⟨(Z i j)⁻¹ • fun l => Z l i, fun l => Z l j, ?_⟩
  ext l k
  simp only [Matrix.sub_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  linear_combination key l k + Z l j * hs i k - Z l i * hs j k

variable [DecidableEq n]

omit [DecidableEq n] in
/-- For a real square matrix $M$ with skew-symmetric part $S = (M - M^T)/2$ and real vectors $x, y$,
$x^T M y - y^T M x = 2 x^T S y$. -/
private theorem dotProduct_mulVec_sub_dotProduct_mulVec (M : Matrix n n ℝ) (x y : n → ℝ) :
    x ⬝ᵥ (M *ᵥ y) - y ⬝ᵥ (M *ᵥ x) = 2 * (x ⬝ᵥ (((1 / 2 : ℝ) • (M - Mᵀ)) *ᵥ y)) := by
  rw [smul_mulVec, sub_mulVec, dotProduct_smul, dotProduct_sub, dotProduct_mulVec x Mᵀ,
    vecMul_transpose, dotProduct_comm (M *ᵥ x) y, smul_eq_mul]
  ring

/-- Let $M$ be a real square matrix, let $S = (M - M^T)/2$ and $\mu = \|S\|_2$, and let $u, v$ be
real vectors with $u^T u = v^T v = 1$, $u^T v = 0$ and $S v = \mu u$. Then $\mu (u v^T - v u^T)$
minimizes $\|M - Z\|_F$ over the real matrices $Z$ with $Z^T = -Z$ and
$\operatorname{rank} Z \le 2$. This is Lemma 12.3.3 of [golub2013matrix].

The book assumes $S [u \mid v] = [u \mid v] \begin{bmatrix} 0 & \mu \\ -\mu & 0 \end{bmatrix}$;
its other half $S u = -\mu v$ is not needed. The book states the lemma for
$\operatorname{rank} Z = 2$. This fails when $S = 0$, as in Lemma 12.3.2; the condition
$\operatorname{rank} Z \le 2$ is the correct reading. The norm $\|S\|_2$ is `Matrix.lpOpNorm 2`.
Every competitor is $x y^T - y x^T$ with $x \perp y$
(`Matrix.exists_eq_vecMulVec_sub_vecMulVec_of_rank_le_two`, then Gram–Schmidt), its squared
distance to $M$ is $\|M\|_F^2 + 2 \|x\|^2 \|y\|^2 - 4 x^T S y$ (`Matrix.norm_sub_skew_sq`), and
$x^T S y \le \mu \|x\| \|y\|$. -/
theorem isMinOn_frobenius_norm_sub_skew_rank_le_two (M : Matrix n n ℝ) {u v : n → ℝ} {μ : ℝ}
    (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) (huv : u ⬝ᵥ v = 0)
    (hSv : ((1 / 2 : ℝ) • (M - Mᵀ)) *ᵥ v = μ • u)
    (hμ : μ = lpOpNorm 2 ((1 / 2 : ℝ) • (M - Mᵀ))) :
    IsMinOn (fun Z => ‖M - Z‖) {Z | Zᵀ = -Z ∧ Z.rank ≤ 2}
      (μ • (vecMulVec u v - vecMulVec v u)) := by
  have hμ0 : 0 ≤ μ := hμ ▸ lpOpNorm_nonneg _ _
  have hopt : ‖M - μ • (vecMulVec u v - vecMulVec v u)‖ ^ 2 = ‖M‖ ^ 2 - 2 * μ ^ 2 := by
    have e : μ • (vecMulVec u v - vecMulVec v u)
        = vecMulVec (μ • u) v - vecMulVec v (μ • u) := by
      rw [smul_sub, smul_vecMulVec, vecMulVec_smul]
    rw [e, norm_sub_skew_sq, dotProduct_mulVec_sub_dotProduct_mulVec, hSv]
    simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul, hu, hv, huv]
    ring
  rintro Z ⟨hZs, hZr⟩
  obtain ⟨x, y, rfl⟩ := exists_eq_vecMulVec_sub_vecMulVec_of_rank_le_two hZs hZr
  -- Gram–Schmidt: replace `y` by its component orthogonal to `x`.
  set y' := y - (x ⬝ᵥ y / x ⬝ᵥ x) • x with hy'
  have hZ' : vecMulVec x y - vecMulVec y x = vecMulVec x y' - vecMulVec y' x := by
    rw [hy', vecMulVec_sub, sub_vecMulVec, vecMulVec_smul, smul_vecMulVec]
    abel
  have hxy' : x ⬝ᵥ y' = 0 := by
    rw [hy', dotProduct_sub, dotProduct_smul, smul_eq_mul]
    by_cases hx : x ⬝ᵥ x = 0
    · rw [dotProduct_self_eq_zero.1 hx]
      simp
    · field_simp
      ring
  have hb := dotProduct_mulVec_le_l2_opNorm ((1 / 2 : ℝ) • (M - Mᵀ)) x y'
  rw [← lpOpNorm_two, ← hμ] at hb
  set a := ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 y'‖
  have ha : a ^ 2 = (x ⬝ᵥ x) * (y' ⬝ᵥ y') := by
    rw [mul_pow, ← dotProduct_self_eq_norm_sq, ← dotProduct_self_eq_norm_sq]
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  change ‖M - μ • (vecMulVec u v - vecMulVec v u)‖ ^ 2
    ≤ ‖M - (vecMulVec x y - vecMulVec y x)‖ ^ 2
  rw [hopt, hZ', norm_sub_skew_sq, dotProduct_mulVec_sub_dotProduct_mulVec, hxy']
  nlinarith [sq_nonneg (a - μ)]

end Lemma1233

end Matrix
