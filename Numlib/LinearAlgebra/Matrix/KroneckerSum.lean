/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.Kronecker`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.LinearAlgebra.Matrix.Kronecker

/-!
# The Kronecker sum and separation of variables

Let $m$ and $n$ be finite index sets, and let $A$ be a square matrix indexed by $m$ and $B$ a square
matrix indexed by $n$. The **Kronecker sum** of $A$ and $B$ is the square matrix
$$A \oplus B = A \otimes I + I \otimes B$$
indexed by $m \times n$. It is the matrix of the operator $x \otimes y \mapsto Ax \otimes y + x
\otimes By$. Mathlib has the Kronecker product $A \otimes B$ and its algebra, but not the Kronecker
sum and no spectral statement about it. This file supplies both. [saad2003iterative], §13.2 writes
the Kronecker sum as $T_x \oplus T_y$ and states its eigenvalues without proof.

The main fact is separation of variables. The elementary tensor $v \otimes w$ has the entries
$(v \otimes w)_{(i, j)} = v_i w_j$, and $(A \oplus B)(v \otimes w) = Av \otimes w + v \otimes Bw$.
Thus if $Av = \sigma v$ and $Bw = \mu w$, then $v \otimes w$ is an eigenvector of $A \oplus B$ for
$\sigma + \mu$. The elementary tensors of two orthonormal bases form an orthonormal basis, because
$\langle v \otimes w, v' \otimes w' \rangle = \langle v, v' \rangle \langle w, w' \rangle$. Hence
these eigenvectors exhaust the space: the spectrum of the Kronecker sum of two diagonalizable
matrices is the set of the sums $\sigma_k + \mu_l$, and a repeated sum still corresponds to
independent eigenvectors. The spectral consequence is also stated without eigenvalues: bounds on the
quadratic forms and coercivity constants add under a Kronecker sum. This is how a two-dimensional
model problem enters a convergence estimate. The five-point Laplacian is the Kronecker sum of two
copies of the tridiagonal Toeplitz matrix of `Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz`, and
the bounds of that module add.

## Main definitions

* `Matrix.kroneckerSum`: the Kronecker sum $A \oplus B = A \otimes I + I \otimes B$.
* `Matrix.kroneckerOrthonormalBasis`: the orthonormal basis $(u_i \otimes u'_j)_{(i, j)}$ of
  $\mathbb{K}^{m \times n}$ made of the elementary tensors of two orthonormal bases $(u_i)$ and
  $(u'_j)$.

## Main results

* `Matrix.kroneckerSum_mulVec_kroneckerVec`: the Leibniz rule $(A \oplus B)(v \otimes w) = Av
  \otimes w + v \otimes Bw$.
* `Matrix.kroneckerSum_mulVec_kroneckerVec_of_mulVec_eq_smul`: if $Av = \sigma v$ and $Bw = \mu w$,
  then $(A \oplus B)(v \otimes w) = (\sigma + \mu)(v \otimes w)$.
* `Matrix.hasEigenvector_kroneckerSum`: the same statement as an eigenvector of the operator on
  $\mathbb{K}^{m \times n}$.
* `Matrix.isCoerciveWith_kroneckerSum`, `Matrix.isSymmetricBoundedBy_kroneckerSum`,
  `Matrix.posDef_kroneckerSum`: coercivity constants and bounds on the quadratic forms add under a
  Kronecker sum, and the Kronecker sum of two positive definite matrices is positive definite.
* `Matrix.kroneckerSum_mulVec_vec`: on the column stacking $\operatorname{vec} X$, the Kronecker sum
  acts as the Sylvester operator $X \mapsto BX + XA^T$.
* `Matrix.kroneckerSum_hasBandwidth`: in the positional layout, the Kronecker sum $A_2 \oplus A_1$
  of a tridiagonal $A_2$ of order $n_2$ and any $A_1$ of order $n_1$ has lower and upper bandwidth
  $n_1$.

## Proof outline

The bounds on quadratic forms are proved without eigenvectors. A vector $z$ indexed by $m \times n$
splits into column fibres $(z_{(i, j)})_{i}$ for fixed $j$, and into row fibres $(z_{(i, j)})_{j}$
for fixed $i$. The quadratic form of $A \otimes I$ is the sum of the quadratic forms of $A$ on the
column fibres, the quadratic form of $I \otimes B$ is the sum of the quadratic forms of $B$ on the
row fibres, and $\|z\|^2$ is the sum of the squared norms of the fibres in either direction.

## Notation

* `A ⊕ₖ B`: `Matrix.kroneckerSum A B`, the Kronecker sum $A \oplus B$. The notation is scoped in
  `Kronecker`, beside Mathlib's `A ⊗ₖ B`.

## Implementation notes

* All matrices here are indexed by the product type `m × n`, as in Mathlib's `Matrix.kroneckerMap`.
  The elementary tensor $v \otimes w$ is `Matrix.kroneckerVec v w` of
  `Numlib.LinearAlgebra.Matrix.Kronecker`, which also has the action `Matrix.kronecker_mulVec` of a
  Kronecker product on it.
* A user that needs the index type `Fin (n₁ * n₂)` reindexes with `Matrix.reindex` and an
  equivalence of `Fin` products. The band statements do this with `finProdFinEquiv`, the positional
  layout of `Numlib.LinearAlgebra.Matrix.Kronecker`, through `Matrix.kroneckerSumFin`.
-/

open scoped Matrix Kronecker

namespace Matrix

/-! ### The Kronecker sum of two matrices -/

section Ring

variable {R : Type*} [CommRing R] {m n : Type*}

section Def

variable [DecidableEq m] [DecidableEq n]

/-- The **Kronecker sum** of a square matrix $A$ indexed by $m$ and a square matrix $B$ indexed by
$n$ is the square matrix
$$A \oplus B = A \otimes I_n + I_m \otimes B$$
indexed by $m \times n$. It is the matrix of the operator $x \otimes y \mapsto Ax \otimes y + x
\otimes By$.

This is equation (13.12) of [saad2003iterative], where it is written $T_x \oplus T_y$. The
scoped notation is `A ⊕ₖ B`. -/
def kroneckerSum (A : Matrix m m R) (B : Matrix n n R) : Matrix (m × n) (m × n) R :=
  A ⊗ₖ (1 : Matrix n n R) + (1 : Matrix m m R) ⊗ₖ B

@[inherit_doc]
scoped[Kronecker] infixl:100 " ⊕ₖ " => Matrix.kroneckerSum

/-- The definition of the Kronecker sum: $A \oplus B = A \otimes I + I \otimes B$. -/
theorem kroneckerSum_def (A : Matrix m m R) (B : Matrix n n R) :
    A ⊕ₖ B = A ⊗ₖ (1 : Matrix n n R) + (1 : Matrix m m R) ⊗ₖ B := rfl

/-- The entries of a Kronecker sum are
$$(A \oplus B)_{(i_1, i_2), (j_1, j_2)} = \delta_{i_2 j_2} A_{i_1 j_1} + \delta_{i_1 j_1} B_{i_2
  j_2}.$$
-/
theorem kroneckerSum_apply (A : Matrix m m R) (B : Matrix n n R) (i₁ j₁ : m) (i₂ j₂ : n) :
    (A ⊕ₖ B) (i₁, i₂) (j₁, j₂)
      = (if i₂ = j₂ then A i₁ j₁ else 0) + (if i₁ = j₁ then B i₂ j₂ else 0) := by
  simp [kroneckerSum, Matrix.one_apply, mul_ite, ite_mul]

/-- The Kronecker sum is additive in the pair $(A, B)$: $(A_1 + A_2) \oplus (B_1 + B_2) = A_1 \oplus
B_1 + A_2 \oplus B_2$. -/
theorem kroneckerSum_add (A₁ A₂ : Matrix m m R) (B₁ B₂ : Matrix n n R) :
    (A₁ + A₂) ⊕ₖ (B₁ + B₂) = A₁ ⊕ₖ B₁ + A₂ ⊕ₖ B₂ := by
  simp only [kroneckerSum, add_kronecker, kronecker_add]
  abel

/-- For a scalar $c$, $(cA) \oplus (cB) = c (A \oplus B)$. -/
theorem kroneckerSum_smul (c : R) (A : Matrix m m R) (B : Matrix n n R) :
    (c • A) ⊕ₖ (c • B) = c • (A ⊕ₖ B) := by
  simp only [kroneckerSum, smul_kronecker, kronecker_smul, smul_add]

/-- The Kronecker sum of two zero matrices is zero. -/
@[simp]
theorem kroneckerSum_zero_zero : (0 : Matrix m m R) ⊕ₖ (0 : Matrix n n R) = 0 := by
  simp [kroneckerSum]

/-- Transposition distributes over a Kronecker sum: $(A \oplus B)^T = A^T \oplus B^T$. -/
theorem transpose_kroneckerSum (A : Matrix m m R) (B : Matrix n n R) :
    (A ⊕ₖ B)ᵀ = Aᵀ ⊕ₖ Bᵀ := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  rw [transpose_apply, kroneckerSum_apply, kroneckerSum_apply, transpose_apply, transpose_apply]
  congr 1 <;> exact if_congr eq_comm rfl rfl

/-- Conjugate transposition distributes over a Kronecker sum: $(A \oplus B)^H = A^H \oplus B^H$. -/
theorem conjTranspose_kroneckerSum [StarRing R] (A : Matrix m m R) (B : Matrix n n R) :
    (A ⊕ₖ B)ᴴ = Aᴴ ⊕ₖ Bᴴ := by
  simp [kroneckerSum, conjTranspose_add, conjTranspose_kronecker]

/-- If $A$ and $B$ are Hermitian, then $A \oplus B$ is Hermitian. -/
theorem isHermitian_kroneckerSum [StarRing R] {A : Matrix m m R} {B : Matrix n n R}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (A ⊕ₖ B).IsHermitian := by
  rw [IsHermitian, conjTranspose_kroneckerSum, hA.eq, hB.eq]

end Def

/-! ### Separation of variables -/

variable [DecidableEq m] [DecidableEq n]

/-- The **Leibniz rule** for a Kronecker sum. Let $R$ be a commutative ring, let $A$ and $B$ be
square matrices over $R$ indexed by finite sets $m$ and $n$, and let $v \in R^m$ and
$w \in R^n$. Then
$$(A \oplus B)(v \otimes w) = Av \otimes w + v \otimes Bw.$$

This is equation (13.13) of [saad2003iterative]. The elementary tensor $v \otimes w$ is
`Matrix.kroneckerVec v w`. -/
theorem kroneckerSum_mulVec_kroneckerVec [Fintype m] [Fintype n] (A : Matrix m m R)
    (B : Matrix n n R) (v : m → R) (w : n → R) :
    (A ⊕ₖ B) *ᵥ kroneckerVec v w = kroneckerVec (A *ᵥ v) w + kroneckerVec v (B *ᵥ w) := by
  rw [kroneckerSum, add_mulVec, kronecker_mulVec, kronecker_mulVec, one_mulVec, one_mulVec]

/-- **Separation of variables.** Let $A$ and $B$ be square matrices over a commutative ring, indexed
by finite sets $m$ and $n$. If $Av = \sigma v$ and $Bw = \mu w$, then
$$(A \oplus B)(v \otimes w) = (\sigma + \mu)(v \otimes w).$$
-/
theorem kroneckerSum_mulVec_kroneckerVec_of_mulVec_eq_smul [Fintype m] [Fintype n]
    {A : Matrix m m R} {B : Matrix n n R} {v : m → R} {w : n → R} {σ μ : R}
    (hv : A *ᵥ v = σ • v) (hw : B *ᵥ w = μ • w) :
    (A ⊕ₖ B) *ᵥ kroneckerVec v w = (σ + μ) • kroneckerVec v w := by
  rw [kroneckerSum_mulVec_kroneckerVec, hv, hw, kroneckerVec_smul_left,
    kroneckerVec_smul_right, add_smul]

/-! ### Vectorization and band structure -/

/-- The Kronecker sum on the column stacking. Let $A$ be a square matrix indexed by $m$, let $B$ be
a square matrix indexed by $n$, and let $X$ be an $n \times m$ matrix, all over a commutative
ring. Then
$$(A \oplus B) \operatorname{vec} X = \operatorname{vec}(BX + XA^T).$$
Hence the linear system $(A \oplus B) \operatorname{vec} X = \operatorname{vec} C$ is the
Sylvester equation $BX + XA^T = C$, as in (4.8.12) of [golub2013matrix].

The column stacking $\operatorname{vec}$ is Mathlib's `Matrix.vec`, which indexes the entry
$X_{ij}$ by the pair $(j, i)$. -/
theorem kroneckerSum_mulVec_vec [Fintype m] [Fintype n] (A : Matrix m m R) (B : Matrix n n R)
    (X : Matrix n m R) : (A ⊕ₖ B) *ᵥ vec X = vec (B * X + X * Aᵀ) := by
  rw [kroneckerSum, add_mulVec, kronecker_mulVec_vec, kronecker_mulVec_vec, Matrix.one_mul,
    transpose_one, Matrix.mul_one, ← vec_add, add_comm]

section Band

variable {n₁ n₂ : ℕ}

/-- The Kronecker sum in the positional layout. For square matrices $A_2$ of order $n_2$ and $A_1$
of order $n_1$, `Matrix.kroneckerSumFin A₂ A₁` is $A_2 \oplus A_1$ with the index $(j, i)$
placed at position $i + n_1 j$ of `Fin (n₂ * n₁)`, as in `Matrix.kroneckerFin`. Its block
$(j, j')$ is $(A_2)_{jj'} I + \delta_{jj'} A_1$. -/
def kroneckerSumFin (A₂ : Matrix (Fin n₂) (Fin n₂) R) (A₁ : Matrix (Fin n₁) (Fin n₁) R) :
    Matrix (Fin (n₂ * n₁)) (Fin (n₂ * n₁)) R :=
  (A₂ ⊕ₖ A₁).submatrix finProdFinEquiv.symm finProdFinEquiv.symm

/-- In the positional layout, the Kronecker sum is $A_2 \otimes I + I \otimes A_1$:
`Matrix.kroneckerSumFin A₂ A₁` equals `Matrix.kroneckerFin A₂ 1 + Matrix.kroneckerFin 1 A₁`. -/
theorem kroneckerSumFin_eq (A₂ : Matrix (Fin n₂) (Fin n₂) R) (A₁ : Matrix (Fin n₁) (Fin n₁) R) :
    kroneckerSumFin A₂ A₁ = kroneckerFin A₂ 1 + kroneckerFin 1 A₁ := by
  rw [kroneckerSumFin, kroneckerSum_def, kroneckerFin, kroneckerFin]
  rfl

/-- Let $A_2$ be a square matrix of order $n_2$ with lower bandwidth $1$, and let $A_1$ be any
square matrix of order $n_1$. Then, in the positional layout, $A_2 \oplus A_1$ has lower
bandwidth $n_1$. The reason is that a block has order $n_1$, and $A_2$ couples only neighbouring
blocks below the diagonal. -/
theorem kroneckerSum_hasLowerBandwidth {A₂ : Matrix (Fin n₂) (Fin n₂) R}
    (A₁ : Matrix (Fin n₁) (Fin n₁) R) (h₂ : A₂.HasLowerBandwidth 1) :
    (kroneckerSumFin A₂ A₁).HasLowerBandwidth n₁ := by
  rw [hasLowerBandwidth_iff_fin] at h₂ ⊢
  intro I J hIJ
  obtain ⟨⟨j, i⟩, rfl⟩ := finProdFinEquiv.surjective I
  obtain ⟨⟨j', i'⟩, rfl⟩ := finProdFinEquiv.surjective J
  simp only [finProdFinEquiv_apply_val] at hIJ
  rw [kroneckerSumFin, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    kroneckerSum_apply]
  have hjj : (j : ℕ) ≠ j' := by
    intro h
    rw [h] at hIJ
    omega
  rw [ite_eq_right fun h : j = j' => hjj (congrArg Fin.val h), add_zero]
  split_ifs with hii
  · subst hii
    refine h₂ j j' ?_
    have : n₁ * ((j' : ℕ) + 1) < n₁ * j := by rw [mul_add_one]; omega
    have := Nat.lt_of_mul_lt_mul_left this
    omega
  · rfl

/-- Let $A_2$ be a square matrix of order $n_2$ with upper bandwidth $1$, and let $A_1$ be any
square matrix of order $n_1$. Then, in the positional layout, $A_2 \oplus A_1$ has upper
bandwidth $n_1$. The proof applies `Matrix.kroneckerSum_hasLowerBandwidth` to the transposes. -/
theorem kroneckerSum_hasUpperBandwidth {A₂ : Matrix (Fin n₂) (Fin n₂) R}
    (A₁ : Matrix (Fin n₁) (Fin n₁) R) (h₂ : A₂.HasUpperBandwidth 1) :
    (kroneckerSumFin A₂ A₁).HasUpperBandwidth n₁ := by
  rw [← hasLowerBandwidth_transpose_iff, kroneckerSumFin, transpose_submatrix,
    transpose_kroneckerSum]
  exact kroneckerSum_hasLowerBandwidth A₁ᵀ (hasLowerBandwidth_transpose_iff.2 h₂)

/-- The **five-point structure.** Let $R$ be a commutative ring, let $A_2$ be a tridiagonal square
matrix of order $n_2$ over $R$, and let $A_1$ be any square matrix of order $n_1$ over $R$.
Then, in the positional layout `Fin (n₂ * n₁)` of `Matrix.kroneckerSumFin`, the Kronecker sum
$A_2 \oplus A_1$ has lower bandwidth $n_1$ and upper bandwidth $n_1$: its entry $(p, q)$ is zero
when $|p - q| > n_1$.

This is the band structure of §4.8.4 of [golub2013matrix]. The source says "bandwidth
$n_1 + 1$", which counts the diagonal. The bandwidths are `Matrix.HasLowerBandwidth` and
`Matrix.HasUpperBandwidth`. -/
theorem kroneckerSum_hasBandwidth {A₂ : Matrix (Fin n₂) (Fin n₂) R}
    (A₁ : Matrix (Fin n₁) (Fin n₁) R) (h₂ : A₂.IsTridiagonal) :
    (kroneckerSumFin A₂ A₁).HasLowerBandwidth n₁ ∧ (kroneckerSumFin A₂ A₁).HasUpperBandwidth n₁ :=
  ⟨kroneckerSum_hasLowerBandwidth A₁ (isTridiagonal_iff_hasBandwidth_one.1 h₂).1,
    kroneckerSum_hasUpperBandwidth A₁ (isTridiagonal_iff_hasBandwidth_one.1 h₂).2⟩

end Band

end Ring

/-! ### The tensor orthonormal basis -/

section RCLike

open scoped ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-- The inner product of two elementary tensors factors:
$$\langle v \otimes w, v' \otimes w' \rangle = \langle v, v' \rangle \langle w, w' \rangle.$$
This identity is the proof that the elementary tensors of two orthonormal bases are orthonormal. -/
theorem kroneckerVec_inner (v v' : m → 𝕜) (w w' : n → 𝕜) :
    inner 𝕜 (WithLp.toLp 2 (kroneckerVec v w)) (WithLp.toLp 2 (kroneckerVec v' w'))
      = inner 𝕜 (WithLp.toLp 2 v) (WithLp.toLp 2 v')
        * inner 𝕜 (WithLp.toLp 2 w) (WithLp.toLp 2 w') := by
  simp only [EuclideanSpace.inner_toLp_toLp, dotProduct, Pi.star_apply, kroneckerVec,
    Fintype.sum_prod_type]
  rw [Fintype.sum_mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    simp only [RCLike.star_def, map_mul]; ring

/-- The $j$-th column fibre $(z_{(i, j)})_{i \in m}$ of a vector $z$ indexed by $m \times n$. -/
private def colFibre (z : EuclideanSpace 𝕜 (m × n)) (j : n) : EuclideanSpace 𝕜 m :=
  WithLp.toLp 2 fun i => WithLp.ofLp z (i, j)

/-- The $i$-th row fibre $(z_{(i, j)})_{j \in n}$ of a vector $z$ indexed by $m \times n$. -/
private def rowFibre (z : EuclideanSpace 𝕜 (m × n)) (i : m) : EuclideanSpace 𝕜 n :=
  WithLp.toLp 2 fun j => WithLp.ofLp z (i, j)

/-- The squared norm of a vector indexed by $m \times n$ is the sum of the squared norms of its
column fibres. -/
private theorem norm_sq_eq_sum_colFibre (z : EuclideanSpace 𝕜 (m × n)) :
    ‖z‖ ^ 2 = ∑ j, ‖colFibre z j‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, colFibre]
  rw [Fintype.sum_prod_type_right]

/-- The squared norm of a vector indexed by $m \times n$ is the sum of the squared norms of its row
fibres. -/
private theorem norm_sq_eq_sum_rowFibre (z : EuclideanSpace 𝕜 (m × n)) :
    ‖z‖ ^ 2 = ∑ i, ‖rowFibre z i‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, rowFibre]
  rw [Fintype.sum_prod_type]

variable [DecidableEq m] [DecidableEq n]

/-- The **tensor orthonormal basis.** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, and let $m$
and $n$ be finite index sets. If $(u_i)_{i \in m}$ is an orthonormal basis of $\mathbb{K}^m$ and
$(u'_j)_{j \in n}$ is an orthonormal basis of $\mathbb{K}^n$, then the elementary tensors
$(u_i \otimes u'_j)_{(i, j) \in m \times n}$ form an orthonormal basis of
$\mathbb{K}^{m \times n}$.

This follows Section 13.2 of [saad2003iterative]. Together with
`Matrix.kroneckerSum_mulVec_kroneckerVec_of_mulVec_eq_smul`, it gives all eigenpairs of the
Kronecker sum of two diagonalizable matrices. The vectors of the basis are given by
`Matrix.kroneckerOrthonormalBasis_apply`. Orthonormality follows from
`Matrix.kroneckerVec_inner`, and the family spans because it has $|m| |n|$ elements. -/
noncomputable def kroneckerOrthonormalBasis (u : OrthonormalBasis m 𝕜 (EuclideanSpace 𝕜 m))
    (u' : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n)) :
    OrthonormalBasis (m × n) 𝕜 (EuclideanSpace 𝕜 (m × n)) :=
  have hon : Orthonormal 𝕜 fun q : m × n => WithLp.toLp 2
      (kroneckerVec (WithLp.ofLp (u q.1)) (WithLp.ofLp (u' q.2))) := by
    refine orthonormal_iff_ite.2 fun q q' => ?_
    rw [kroneckerVec_inner]
    simp only [WithLp.toLp_ofLp]
    rw [orthonormal_iff_ite.1 u.orthonormal, orthonormal_iff_ite.1 u'.orthonormal]
    by_cases h1 : q.1 = q'.1 <;> by_cases h2 : q.2 = q'.2 <;> simp [h1, h2, Prod.ext_iff]
  OrthonormalBasis.mk hon
    (hon.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp [finrank_euclideanSpace])).ge

/-- The vector of `Matrix.kroneckerOrthonormalBasis u u'` at the index $(i, j)$ is the elementary
tensor $u_i \otimes u'_j$. -/
@[simp]
theorem kroneckerOrthonormalBasis_apply (u : OrthonormalBasis m 𝕜 (EuclideanSpace 𝕜 m))
    (u' : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n)) (q : m × n) :
    kroneckerOrthonormalBasis u u' q
      = WithLp.toLp 2 (kroneckerVec (WithLp.ofLp (u q.1)) (WithLp.ofLp (u' q.2))) := by
  rw [kroneckerOrthonormalBasis, OrthonormalBasis.coe_mk]

/-- The **eigenpairs of a Kronecker sum.** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, and let
$A$ and $B$ be square matrices over $\mathbb{K}$ indexed by finite sets $m$ and $n$. If
$v \neq 0$, $w \neq 0$, $Av = \sigma v$ and $Bw = \mu w$, then $v \otimes w$ is an eigenvector
of $A \oplus B$ for the eigenvalue $\sigma + \mu$.

This corresponds to (13.13) of [saad2003iterative]. The eigenvector is stated for the operator
`Matrix.toEuclideanLin (A ⊕ₖ B)` on `EuclideanSpace 𝕜 (m × n)`, with
`Module.End.HasEigenvector`. The vector $v \otimes w$ is nonzero because $v$ and $w$ are
nonzero. -/
theorem hasEigenvector_kroneckerSum {A : Matrix m m 𝕜} {B : Matrix n n 𝕜} {v : m → 𝕜}
    {w : n → 𝕜} {σ μ : 𝕜} (hv : A *ᵥ v = σ • v) (hw : B *ᵥ w = μ • w) (hv0 : v ≠ 0)
    (hw0 : w ≠ 0) :
    Module.End.HasEigenvector (toEuclideanLin (A ⊕ₖ B)) (σ + μ)
      (WithLp.toLp 2 (kroneckerVec v w)) := by
  refine ⟨Module.End.mem_eigenspace_iff.2 ?_, ?_⟩
  · change WithLp.toLp 2 ((A ⊕ₖ B) *ᵥ kroneckerVec v w) = _
    rw [kroneckerSum_mulVec_kroneckerVec_of_mulVec_eq_smul hv hw]
    rfl
  · simpa using kroneckerVec_ne_zero hv0 hw0

/-! ### Quadratic-form bounds add -/

/-- The quadratic form of $A \otimes I$ at $z$ is the sum of the quadratic forms of $A$ at the
column fibres of $z$. -/
private theorem inner_kronecker_one_left (A : Matrix m m 𝕜) (z : EuclideanSpace 𝕜 (m × n)) :
    inner 𝕜 (toEuclideanLin (A ⊗ₖ (1 : Matrix n n 𝕜)) z) z
      = ∑ j, inner 𝕜 (toEuclideanLin A (colFibre z j)) (colFibre z j) := by
  have hfib : ∀ (i : m) (j : n), ((A ⊗ₖ (1 : Matrix n n 𝕜)) *ᵥ WithLp.ofLp z) (i, j)
      = (A *ᵥ WithLp.ofLp (colFibre z j)) i := by
    intro i j
    simp [colFibre, mulVec_apply_eq_sum, Fintype.sum_prod_type, Matrix.one_apply]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply]
  rw [Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [show WithLp.ofLp (toEuclideanLin (A ⊗ₖ (1 : Matrix n n 𝕜)) z)
    = (A ⊗ₖ (1 : Matrix n n 𝕜)) *ᵥ WithLp.ofLp z from rfl, hfib i j]
  rfl

/-- The quadratic form of $I \otimes B$ at $z$ is the sum of the quadratic forms of $B$ at the row
fibres of $z$. -/
private theorem inner_one_kronecker_right (B : Matrix n n 𝕜) (z : EuclideanSpace 𝕜 (m × n)) :
    inner 𝕜 (toEuclideanLin ((1 : Matrix m m 𝕜) ⊗ₖ B) z) z
      = ∑ i, inner 𝕜 (toEuclideanLin B (rowFibre z i)) (rowFibre z i) := by
  have hfib : ∀ (i : m) (j : n), (((1 : Matrix m m 𝕜) ⊗ₖ B) *ᵥ WithLp.ofLp z) (i, j)
      = (B *ᵥ WithLp.ofLp (rowFibre z i)) j := by
    intro i j
    simp [rowFibre, mulVec_apply_eq_sum, Fintype.sum_prod_type, Matrix.one_apply]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show WithLp.ofLp (toEuclideanLin ((1 : Matrix m m 𝕜) ⊗ₖ B) z)
    = ((1 : Matrix m m 𝕜) ⊗ₖ B) *ᵥ WithLp.ofLp z from rfl, hfib i j]
  rfl

/-- The real part of the quadratic form of $A \oplus B$ at $z$ is the sum of the real parts of the
quadratic forms of $A$ at the column fibres of $z$ and of $B$ at the row fibres of $z$. -/
private theorem re_inner_kroneckerSum (A : Matrix m m 𝕜) (B : Matrix n n 𝕜)
    (z : EuclideanSpace 𝕜 (m × n)) :
    RCLike.re (inner 𝕜 (toEuclideanLin (A ⊕ₖ B) z) z)
      = (∑ j, RCLike.re (inner 𝕜 (toEuclideanLin A (colFibre z j)) (colFibre z j)))
        + ∑ i, RCLike.re (inner 𝕜 (toEuclideanLin B (rowFibre z i)) (rowFibre z i)) := by
  rw [kroneckerSum_def, map_add, LinearMap.add_apply, inner_add_left, map_add,
    inner_kronecker_one_left, inner_one_kronecker_right, map_sum, map_sum]

/-- Coercivity constants add under a Kronecker sum. Let $A$ and $B$ be square matrices over
$\mathbb{K}$ indexed by finite sets $m$ and $n$. If $c_1 \|x\|^2 \le \operatorname{Re} \langle
Ax, x \rangle$ for all $x \in \mathbb{K}^m$ and $c_2 \|y\|^2 \le \operatorname{Re} \langle By, y
\rangle$ for all $y \in \mathbb{K}^n$, then
$$(c_1 + c_2) \|z\|^2 \le \operatorname{Re} \langle (A \oplus B) z, z \rangle \qquad \text{for
  all } z \in \mathbb{K}^{m \times n}.$$
-/
theorem isCoerciveWith_kroneckerSum {A : Matrix m m 𝕜} {B : Matrix n n 𝕜} {c₁ c₂ : ℝ}
    (hA : (toEuclideanLin A).IsCoerciveWith c₁) (hB : (toEuclideanLin B).IsCoerciveWith c₂) :
    (toEuclideanLin (A ⊕ₖ B)).IsCoerciveWith (c₁ + c₂) := by
  intro z
  rw [re_inner_kroneckerSum, add_mul]
  refine add_le_add ?_ ?_
  · rw [norm_sq_eq_sum_colFibre z, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => hA (colFibre z j)
  · rw [norm_sq_eq_sum_rowFibre z, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hB (rowFibre z i)

/-- **Bounds on quadratic forms add** under a Kronecker sum. Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$, and let $A$ and $B$ be square matrices over $\mathbb{K}$ indexed by finite sets
$m$ and $n$. Suppose that $A$ is Hermitian with $a_1 \|x\|^2 \le \operatorname{Re} \langle Ax, x
\rangle \le b_1 \|x\|^2$ for all $x$, and that $B$ is Hermitian with $a_2 \|y\|^2 \le
\operatorname{Re} \langle By, y \rangle \le b_2 \|y\|^2$ for all $y$. Then $A \oplus B$ is
Hermitian and
$$(a_1 + a_2) \|z\|^2 \le \operatorname{Re} \langle (A \oplus B) z, z \rangle \le (b_1 + b_2)
  \|z\|^2 \qquad \text{for all } z.$$

This corresponds to (13.14) of [saad2003iterative]. It is the form in which a two-dimensional
model problem enters a convergence estimate, and it names no eigenvalue. The hypotheses and the
conclusion are `LinearMap.IsSymmetricBoundedBy` for the operators `Matrix.toEuclideanLin`. -/
theorem isSymmetricBoundedBy_kroneckerSum {A : Matrix m m 𝕜} {B : Matrix n n 𝕜}
    {a₁ b₁ a₂ b₂ : ℝ} (hA : (toEuclideanLin A).IsSymmetricBoundedBy a₁ b₁)
    (hB : (toEuclideanLin B).IsSymmetricBoundedBy a₂ b₂) :
    (toEuclideanLin (A ⊕ₖ B)).IsSymmetricBoundedBy (a₁ + a₂) (b₁ + b₂) := by
  refine ⟨isSymmetric_toEuclideanLin_iff.2 (isHermitian_kroneckerSum
    (isSymmetric_toEuclideanLin_iff.1 hA.isSymmetric)
    (isSymmetric_toEuclideanLin_iff.1 hB.isSymmetric)), fun z => ?_, fun z => ?_⟩
  · exact isCoerciveWith_kroneckerSum hA.isCoerciveWith hB.isCoerciveWith z
  · rw [re_inner_kroneckerSum, add_mul]
    refine add_le_add ?_ ?_
    · rw [norm_sq_eq_sum_colFibre z, Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => hA.re_inner_le (colFibre z j)
    · rw [norm_sq_eq_sum_rowFibre z, Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => hB.re_inner_le (rowFibre z i)

end RCLike

open scoped ComplexOrder in
/-- Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, and let $A$ and $B$ be square matrices over
$\mathbb{K}$ indexed by finite sets $m$ and $n$. If $A$ and $B$ are positive definite, then
$A \oplus B$ is positive definite. -/
theorem posDef_kroneckerSum {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Finite m] [Finite n]
    [DecidableEq m] [DecidableEq n] {A : Matrix m m 𝕜} {B : Matrix n n 𝕜} (hA : A.PosDef)
    (hB : B.PosDef) : (A ⊕ₖ B).PosDef := by
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  rw [posDef_iff_isSymmetricCoercive] at hA hB ⊢
  obtain ⟨c₁, hc₁, hA'⟩ := hA.isCoercive
  obtain ⟨c₂, hc₂, hB'⟩ := hB.isCoercive
  exact ⟨isSymmetric_toEuclideanLin_iff.2 (isHermitian_kroneckerSum
      (isSymmetric_toEuclideanLin_iff.1 hA.isSymmetric)
      (isSymmetric_toEuclideanLin_iff.1 hB.isSymmetric)),
    c₁ + c₂, by linarith, isCoerciveWith_kroneckerSum hA' hB'⟩

end Matrix
