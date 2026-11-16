/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Order.SuccPred.Nat
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.UnitaryGroup
import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.LinearAlgebra.Matrix.Similar

/-!
# Unreduced upper Hessenberg matrices and Krylov matrices

An upper Hessenberg matrix $H$ is *unreduced* when none of its subdiagonal entries $h_{i+1,i}$ is
zero ([golub2013matrix], §7.4.5). Unreducedness makes the Hessenberg form of a matrix essentially
unique (the implicit Q theorem, `Matrix.IsArnoldiDecomposition.implicitQ` in
`Numlib.LinearAlgebra.Matrix.KrylovDecomposition`), gives every eigenvalue geometric multiplicity
one, and lets a QR step be computed implicitly.

The module proves these facts through the **Krylov matrix** $K(A, v, j) = [v \mid A v \mid \cdots
\mid A^{j-1} v]$. For an upper Hessenberg $(N+1) \times (N+1)$ matrix $H$ and the first unit vector
$e_0$, the Krylov matrix $K(H, e_0, N + 1)$ is upper triangular, and its diagonal entries are the
partial products of the subdiagonal of $H$. Thus $H$ is unreduced exactly when this Krylov matrix is
also nonsingular, and conjugation by a unitary $Q$ gives Theorem 7.4.3 of [golub2013matrix].

## Main definitions

* `Matrix.IsUnreducedUpperHessenberg`: $H$ is upper Hessenberg and every subdiagonal entry is
  nonzero.
* `Matrix.krylovMatrix`: the Krylov matrix $K(A, v, j) = [v \mid A v \mid \cdots \mid A^{j-1} v]$.

## Main results

* `Matrix.IsUnreducedUpperHessenberg.linearIndependent_init_cols`,
  `Matrix.IsUnreducedUpperHessenberg.finrank_eigenspace_le_one`: the first $N$ columns of an
  unreduced upper Hessenberg $(N+1) \times (N+1)$ matrix are linearly independent, so every
  eigenvalue has geometric multiplicity one (Theorem 7.4.4 of [golub2013matrix]).
* `Matrix.IsUpperHessenberg.isUpperTriangular_krylovMatrix`,
  `Matrix.IsUpperHessenberg.krylovMatrix_succ_succ`: the Krylov matrix of an upper Hessenberg matrix
  on $e_0$ is upper triangular, and its diagonal is the sequence of partial products of the
  subdiagonal.
* `Matrix.isUnreducedUpperHessenberg_conj_iff_krylovMatrix`: for unitary $Q$, the matrix $Q^H A Q$
  is unreduced upper Hessenberg if and only if $Q^H K(A, Q e_0, N + 1)$ is upper triangular and
  nonsingular (Theorem 7.4.3 of [golub2013matrix]).
* `Matrix.IsUnreducedUpperHessenberg.mul_mul_inv_of_isUpperTriangular`: conjugation by a nonsingular
  upper triangular matrix keeps unreducedness.
* `Matrix.IsUnreducedUpperHessenberg.isUpperTriangular_star_mul_aeval`: the implicit-shift principle
  behind the Francis and QZ steps. If $H$ is unreduced, $Z$ is unitary, $Z^H H Z$ is upper
  Hessenberg and $Z e_0$ is a multiple of $p(H) e_0$, then $Z^H p(H)$ is upper triangular. Thus $Z$
  is the unitary factor of a QR factorization of $p(H)$, computed without forming $p(H)$.

## Proof outline

The implicit-shift principle is proved through Krylov matrices, not through the implicit Q theorem.
Let $K = K(H, e_0, N + 1)$, which is upper triangular and nonsingular. Then $Z^H p(H) K$ is a
multiple of $K(Z^H H Z, e_0, N + 1)$, which is upper triangular because $Z^H H Z$ is Hessenberg; and
$K^{-1}$ is upper triangular. No nonsingularity of $p(H)$ is needed.

## Implementation notes

* Like `Matrix.IsUpperHessenberg`, `Matrix.IsUnreducedUpperHessenberg` is stated for any linearly
  ordered index type. The subdiagonal consists of the entries $h_{ij}$ where $i$ covers $j$
  ($j \lessdot i$); on $\{0, \dots, N - 1\}$ this means $i = j + 1$
  (`Matrix.isUnreducedUpperHessenberg_iff_fin`).
* Indices start at $0$. The statements about Krylov matrices are about $(N+1) \times (N+1)$
  matrices, so that the first unit vector $e_0$, `Pi.single 0 1`, is well typed. The subdiagonal
  entries are then `H i.succ i.castSucc` for `i : Fin N`.
-/

open Polynomial

namespace Matrix

section Basic

variable {n R : Type*} [LinearOrder n]

/-- An **unreduced upper Hessenberg** matrix ([golub2013matrix], §7.4.5: "Hessenberg matrices with
no zero subdiagonal entries are said to be unreduced"). Let $H$ be a square matrix with a
linearly ordered index set. Then $H$ is unreduced upper Hessenberg if $H$ is upper Hessenberg
and $h_{ij} \neq 0$ whenever $i$ covers $j$, that is, whenever $h_{ij}$ is on the subdiagonal. -/
def IsUnreducedUpperHessenberg [Zero R] (H : Matrix n n R) : Prop :=
  H.IsUpperHessenberg ∧ ∀ i j : n, j ⋖ i → H i j ≠ 0

variable [Zero R] {H : Matrix n n R}

/-- An unreduced upper Hessenberg matrix is upper Hessenberg. -/
theorem IsUnreducedUpperHessenberg.isUpperHessenberg (h : H.IsUnreducedUpperHessenberg) :
    H.IsUpperHessenberg :=
  h.1

/-- If $H$ is unreduced upper Hessenberg and $i$ covers $j$, then $h_{ij} \neq 0$: the subdiagonal
entries are nonzero. -/
theorem IsUnreducedUpperHessenberg.apply_ne_zero (h : H.IsUnreducedUpperHessenberg) {i j : n}
    (hij : j ⋖ i) : H i j ≠ 0 :=
  h.2 i j hij

/-- Let $H$ be an $N \times N$ matrix with indices $0, \dots, N - 1$. Then $H$ is unreduced upper
Hessenberg if and only if $H$ is upper Hessenberg and $h_{k+1,k} \neq 0$ for every $k$ with
$k + 1 < N$. -/
theorem isUnreducedUpperHessenberg_iff_fin {N : ℕ} {H : Matrix (Fin N) (Fin N) R} :
    H.IsUnreducedUpperHessenberg ↔
      H.IsUpperHessenberg ∧ ∀ (k : ℕ) (hk : k + 1 < N), H ⟨k + 1, hk⟩ ⟨k, by omega⟩ ≠ 0 := by
  refine and_congr Iff.rfl ⟨fun h k hk => h _ _ ?_, fun h i j hij => ?_⟩
  · rw [Fin.covBy_iff, Order.covBy_iff_add_one_eq]
  · rw [Fin.covBy_iff, Order.covBy_iff_add_one_eq] at hij
    obtain ⟨i, hi⟩ := i
    obtain ⟨j, hj⟩ := j
    simp only at hij
    subst hij
    exact h j hi

/-- Let $H$ be an $(N+1) \times (N+1)$ matrix with indices $0, \dots, N$. Then $H$ is unreduced
upper Hessenberg if and only if $H$ is upper Hessenberg and $h_{i+1,i} \neq 0$ for every
$i < N$. -/
theorem isUnreducedUpperHessenberg_iff_succ {N : ℕ} {H : Matrix (Fin (N + 1)) (Fin (N + 1)) R} :
    H.IsUnreducedUpperHessenberg ↔
      H.IsUpperHessenberg ∧ ∀ i : Fin N, H i.succ i.castSucc ≠ 0 := by
  rw [isUnreducedUpperHessenberg_iff_fin]
  exact and_congr Iff.rfl ⟨fun h i => h i (by omega), fun h k hk => h ⟨k, by omega⟩⟩

/-- If $H$ is an unreduced upper Hessenberg $(N+1) \times (N+1)$ matrix, then $h_{i+1,i} \neq 0$ for
every $i < N$. -/
theorem IsUnreducedUpperHessenberg.apply_succ_castSucc_ne_zero {N : ℕ}
    {H : Matrix (Fin (N + 1)) (Fin (N + 1)) R} (h : H.IsUnreducedUpperHessenberg) (i : Fin N) :
    H i.succ i.castSucc ≠ 0 :=
  (isUnreducedUpperHessenberg_iff_succ.1 h).2 i

/-- Let $f$ be an injective map with $f(0) = 0$ (for example `Complex.ofReal`, or the
complexification of a real matrix). If $H$ is unreduced upper Hessenberg, then so is the matrix
$(f(h_{ij}))$. -/
theorem IsUnreducedUpperHessenberg.map {S F : Type*} [Zero S] [FunLike F R S]
    [ZeroHomClass F R S] {f : F} (hf : Function.Injective f) (h : H.IsUnreducedUpperHessenberg) :
    (H.map f).IsUnreducedUpperHessenberg :=
  ⟨fun i j hij => by rw [map_apply, h.1 i j hij, map_zero],
    fun i j hij => by rw [map_apply]; exact (map_ne_zero_iff f hf).2 (h.2 i j hij)⟩

end Basic

section Shift

variable {n R : Type*} [LinearOrder n] [DecidableEq n] [NonAssocRing R] {H : Matrix n n R}

/-- A shift keeps unreducedness: if $H$ is unreduced upper Hessenberg, then so is $H - \mu I$ for
every scalar $\mu$. The subdiagonal of $H - \mu I$ is that of $H$. -/
theorem IsUnreducedUpperHessenberg.sub_smul_one (h : H.IsUnreducedUpperHessenberg) (μ : R) :
    (H - μ • 1).IsUnreducedUpperHessenberg := by
  refine ⟨h.1.sub_smul_one μ, fun i j hij => ?_⟩
  rw [Matrix.sub_apply, Matrix.smul_apply, one_apply_ne hij.lt.ne', smul_zero, sub_zero]
  exact h.2 i j hij

/-- If $H$ is unreduced upper Hessenberg, then so is $H + \mu I$ for every scalar $\mu$. -/
theorem IsUnreducedUpperHessenberg.add_smul_one (h : H.IsUnreducedUpperHessenberg) (μ : R) :
    (H + μ • 1).IsUnreducedUpperHessenberg := by
  refine ⟨h.1.add_smul_one μ, fun i j hij => ?_⟩
  rw [Matrix.add_apply, Matrix.smul_apply, one_apply_ne hij.lt.ne', smul_zero, add_zero]
  exact h.2 i j hij

end Shift

/-! ### Independence of the leading columns, and geometric multiplicity one -/

section Columns

variable {K : Type*} [Field K] {N : ℕ} {H : Matrix (Fin (N + 1)) (Fin (N + 1)) K}

/-- Let $H$ be an unreduced upper Hessenberg $(N+1) \times (N+1)$ matrix over a field. The
$N \times N$ matrix obtained from $H$ by deleting the first row and the last column is upper
triangular, and its diagonal is the subdiagonal of $H$. Hence its determinant is nonzero. -/
theorem IsUnreducedUpperHessenberg.det_submatrix_succ_castSucc_ne_zero
    (h : H.IsUnreducedUpperHessenberg) : (H.submatrix Fin.succ Fin.castSucc).det ≠ 0 := by
  have hSt : (H.submatrix Fin.succ Fin.castSucc).IsUpperTriangular := by
    intro i j hji
    rw [submatrix_apply]
    refine (isUpperHessenberg_iff_fin.1 h.1) _ _ ?_
    simp only [Fin.val_succ, Fin.val_castSucc]
    have : (j : ℕ) < i := hji
    omega
  rw [det_of_isUpperTriangular hSt, Finset.prod_ne_zero_iff]
  exact fun i _ => h.apply_succ_castSucc_ne_zero i

/-- Let $H$ be an unreduced upper Hessenberg $(N+1) \times (N+1)$ matrix over a field. Then the
first $N$ columns of $H$ are linearly independent.

After deletion of the first row, these columns form an upper triangular matrix whose diagonal is
the subdiagonal of $H$, which has no zero entry. -/
theorem IsUnreducedUpperHessenberg.linearIndependent_init_cols
    (h : H.IsUnreducedUpperHessenberg) :
    LinearIndependent K fun j : Fin N => H.col j.castSucc :=
  LinearIndependent.of_comp (LinearMap.funLeft K K Fin.succ)
    (linearIndependent_cols_of_det_ne_zero h.det_submatrix_succ_castSucc_ne_zero)

/-- Let $H$ be an unreduced upper Hessenberg $(N+1) \times (N+1)$ matrix over a field. Then
$\operatorname{rank} H \ge N$, stated as $N \le \dim \operatorname{range} H$. -/
theorem IsUnreducedUpperHessenberg.le_finrank_range (h : H.IsUnreducedUpperHessenberg) :
    N ≤ Module.finrank K (LinearMap.range (toLin' H)) := by
  have hli := h.linearIndependent_init_cols
  have hle : Submodule.span K (Set.range fun j : Fin N => H.col j.castSucc) ≤
      LinearMap.range (toLin' H) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact ⟨Pi.single j.castSucc 1, by rw [toLin'_apply, mulVec_single_one]⟩
  calc N = Fintype.card (Fin N) := (Fintype.card_fin N).symm
    _ = Module.finrank K (Submodule.span K (Set.range fun j : Fin N => H.col j.castSucc)) :=
      (finrank_span_eq_card hli).symm
    _ ≤ _ := Submodule.finrank_mono hle

/-- Let $H$ be an unreduced upper Hessenberg $(N+1) \times (N+1)$ matrix over a field $K$. Then for
every $\mu \in K$ the eigenspace $\ker (H - \mu I)$ has dimension at most $1$. Thus every
eigenvalue of $H$ has geometric multiplicity one. This is Theorem 7.4.4 of [golub2013matrix].

The matrix $H - \mu I$ is again unreduced, so its rank is at least $N$, and the rank–nullity
theorem leaves at most one dimension for the kernel. The eigenspace is that of
`Matrix.toLin' H`. -/
theorem IsUnreducedUpperHessenberg.finrank_eigenspace_le_one (h : H.IsUnreducedUpperHessenberg)
    (μ : K) : Module.finrank K (Module.End.eigenspace (toLin' H) μ) ≤ 1 := by
  have hμ : toLin' H - μ • (1 : Module.End K (Fin (N + 1) → K)) = toLin' (H - μ • 1) := by
    rw [map_sub, map_smul, toLin'_one, Module.End.one_eq_id]
  have hrank := (h.sub_smul_one μ).le_finrank_range
  have hsum := LinearMap.finrank_range_add_finrank_ker (toLin' (H - μ • 1))
  rw [Module.finrank_fin_fun] at hsum
  rw [Module.End.eigenspace_def, hμ]
  omega

/-- Let $H$ be an unreduced upper Hessenberg $(N+1) \times (N+1)$ matrix over a field. If $\mu$ is
an eigenvalue of $H$, then the eigenspace of $\mu$ has dimension exactly $1$. -/
theorem IsUnreducedUpperHessenberg.finrank_eigenspace_eq_one (h : H.IsUnreducedUpperHessenberg)
    {μ : K} (hμ : Module.End.HasEigenvalue (toLin' H) μ) :
    Module.finrank K (Module.End.eigenspace (toLin' H) μ) = 1 := by
  refine le_antisymm (h.finrank_eigenspace_le_one μ) ?_
  rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
  exact Module.End.hasEigenvalue_iff.1 hμ

end Columns

/-! ### Krylov matrices -/

section Krylov

variable {n R : Type*} [Fintype n] [DecidableEq n]

section Semiring

variable [Semiring R]

/-- The **Krylov matrix** ([golub2013matrix], §7.4.5). Let $A$ be an $n \times n$ matrix over a
semiring, $v$ a vector and $j \in \mathbb{N}$. The Krylov matrix
$$K(A, v, j) = [v \mid A v \mid \cdots \mid A^{j-1} v]$$
is the $n \times j$ matrix whose column $k$ is $A^k v$, for $k = 0, \dots, j - 1$. -/
def krylovMatrix (A : Matrix n n R) (v : n → R) (j : ℕ) : Matrix n (Fin j) R :=
  Matrix.of fun i k => (A ^ (k : ℕ) *ᵥ v) i

/-- The entry $(i, k)$ of $K(A, v, j)$ is the entry $i$ of $A^k v$. -/
@[simp]
theorem krylovMatrix_apply (A : Matrix n n R) (v : n → R) (j : ℕ) (i : n) (k : Fin j) :
    krylovMatrix A v j i k = (A ^ (k : ℕ) *ᵥ v) i :=
  rfl

/-- The column $k$ of $K(A, v, j)$ is the Krylov vector $A^k v$. -/
theorem col_krylovMatrix (A : Matrix n n R) (v : n → R) (j : ℕ) (k : Fin j) :
    (krylovMatrix A v j).col k = A ^ (k : ℕ) *ᵥ v :=
  rfl

/-- The column $k$ of $A \, K(A, v, j)$ is $A^{k+1} v$, that is,
$A \, K(A, v, j) = [A v \mid \cdots \mid A^j v]$. -/
theorem col_mul_krylovMatrix (A : Matrix n n R) (v : n → R) (j : ℕ) (k : Fin j) :
    (A * krylovMatrix A v j).col k = A ^ ((k : ℕ) + 1) *ᵥ v := by
  rw [col_mul_eq_mulVec_col, col_krylovMatrix, mulVec_mulVec, pow_succ']

end Semiring

section CommRing

variable [CommRing R]

/-- The Krylov matrix is linear in the starting vector: $K(A, c v, j) = c \, K(A, v, j)$ for every
scalar $c$. -/
theorem krylovMatrix_smul (A : Matrix n n R) (c : R) (v : n → R) (j : ℕ) :
    krylovMatrix A (c • v) j = c • krylovMatrix A v j := by
  ext i k
  simp [mulVec_smul]

/-- Let $A$ be a square matrix over a commutative ring and $p$ a polynomial. Then
$$p(A) \, K(A, v, j) = K(A, p(A) v, j),$$
since $p(A)$ commutes with every power of $A$. -/
theorem aeval_mul_krylovMatrix (A : Matrix n n R) (p : R[X]) (v : n → R) (j : ℕ) :
    aeval A p * krylovMatrix A v j = krylovMatrix A (aeval A p *ᵥ v) j := by
  ext i k
  change (aeval A p * krylovMatrix A v j).col k i = _
  rw [col_mul_eq_mulVec_col, col_krylovMatrix, krylovMatrix_apply, mulVec_mulVec, mulVec_mulVec]
  have hcomm : aeval A p * A ^ (k : ℕ) = A ^ (k : ℕ) * aeval A p := by
    rw [← aeval_X_pow (R := R) A, ← map_mul, ← map_mul, mul_comm]
  rw [hcomm]

/-- Let $Q$ be a unitary $n \times n$ matrix over a commutative ring with involution, $A$ an
$n \times n$ matrix and $w$ a vector. Then
$$Q^H K(A, Q w, j) = K(Q^H A Q, w, j).$$
With $w = e_0$ and $j = n$ this is the identity $Q^H K(A, Q e_0, n) = [e_0 \mid H e_0 \mid
\cdots \mid H^{n-1} e_0]$ with $H = Q^H A Q$, from the proof of Theorem 7.4.3 of
[golub2013matrix]. -/
theorem conjTranspose_mul_krylovMatrix [StarRing R] {Q : Matrix n n R}
    (hQ : Q ∈ unitaryGroup n R) (A : Matrix n n R) (w : n → R) (j : ℕ) :
    star Q * krylovMatrix A (Q *ᵥ w) j = krylovMatrix (star Q * A * Q) w j := by
  ext i k
  change (star Q * krylovMatrix A (Q *ᵥ w) j).col k i = (krylovMatrix _ w j).col k i
  rw [col_mul_eq_mulVec_col, col_krylovMatrix, col_krylovMatrix, conj_pow_of_mem_unitaryGroup hQ,
    mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

end CommRing

end Krylov

/-! ### The Krylov matrix of a Hessenberg matrix on the first unit vector -/

section HessenbergKrylov

variable {R : Type*} {N : ℕ}

section Semiring

variable [Semiring R] {H : Matrix (Fin (N + 1)) (Fin (N + 1)) R}

/-- Let $H$ be an upper Hessenberg $(N+1) \times (N+1)$ matrix over a semiring. Then the entry $i$
of $H^k e_0$ is zero for every $i > k$. -/
theorem IsUpperHessenberg.pow_mulVec_single_zero_apply_of_lt (hH : H.IsUpperHessenberg)
    {k : ℕ} {i : Fin (N + 1)} (hki : k < i) : (H ^ k *ᵥ Pi.single 0 1) i = 0 := by
  induction k generalizing i with
  | zero =>
    rw [pow_zero, one_mulVec, Pi.single_apply, ite_eq_right_iff]
    intro hi
    subst hi
    exact absurd hki (lt_irrefl _)
  | succ k ih =>
    rw [pow_succ', ← mulVec_mulVec, mulVec, dotProduct]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge k l with hl | hl
    · rw [ih hl, mul_zero]
    · rw [isUpperHessenberg_iff_fin.1 hH i l (by omega), zero_mul]

/-- Let $H$ be an upper Hessenberg $(N+1) \times (N+1)$ matrix over a semiring. Then the Krylov
matrix $K(H, e_0, N + 1)$ is upper triangular. -/
theorem IsUpperHessenberg.isUpperTriangular_krylovMatrix (hH : H.IsUpperHessenberg) :
    (krylovMatrix H (Pi.single 0 1) (N + 1)).IsUpperTriangular :=
  fun _ _ hji => hH.pow_mulVec_single_zero_apply_of_lt hji

/-- For every $(N+1) \times (N+1)$ matrix $H$, the entry $(0, 0)$ of $K(H, e_0, N + 1)$ is $1$. -/
theorem krylovMatrix_single_zero_zero (H : Matrix (Fin (N + 1)) (Fin (N + 1)) R) :
    krylovMatrix H (Pi.single 0 1) (N + 1) 0 0 = 1 := by
  simp

/-- Let $H$ be an upper Hessenberg $(N+1) \times (N+1)$ matrix over a semiring, and let
$K = K(H, e_0, N + 1)$. Then for every $i < N$
$$K_{i+1,i+1} = h_{i+1,i} \, K_{ii}.$$
Since $K_{00} = 1$, the diagonal of $K$ is the sequence of partial products of the subdiagonal
of $H$. -/
theorem IsUpperHessenberg.krylovMatrix_succ_succ (hH : H.IsUpperHessenberg) (i : Fin N) :
    krylovMatrix H (Pi.single 0 1) (N + 1) i.succ i.succ =
      H i.succ i.castSucc * krylovMatrix H (Pi.single 0 1) (N + 1) i.castSucc i.castSucc := by
  simp only [krylovMatrix_apply, Fin.val_succ, Fin.val_castSucc]
  rw [pow_succ', ← mulVec_mulVec, mulVec, dotProduct, Finset.sum_eq_single i.castSucc]
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with hl | hl
    · rw [isUpperHessenberg_iff_fin.1 hH _ _ (by
        simp only [Fin.val_succ]; have : (l : ℕ) < i := hl; omega), zero_mul]
    · rw [hH.pow_mulVec_single_zero_apply_of_lt (by
        rw [Fin.lt_def, Fin.val_castSucc] at hl; exact hl), mul_zero]
  · simp

end Semiring

variable {K : Type*} [Field K] {H : Matrix (Fin (N + 1)) (Fin (N + 1)) K}

/-- Let $H$ be an unreduced upper Hessenberg $(N+1) \times (N+1)$ matrix over a field. Then every
diagonal entry of $K(H, e_0, N + 1)$ is nonzero. -/
theorem IsUnreducedUpperHessenberg.krylovMatrix_apply_self_ne_zero
    (h : H.IsUnreducedUpperHessenberg) (i : Fin (N + 1)) :
    krylovMatrix H (Pi.single 0 1) (N + 1) i i ≠ 0 := by
  induction i using Fin.induction with
  | zero => rw [krylovMatrix_single_zero_zero]; exact one_ne_zero
  | succ i ih =>
    rw [h.1.krylovMatrix_succ_succ]
    exact mul_ne_zero (h.apply_succ_castSucc_ne_zero i) ih

/-- Let $H$ be an unreduced upper Hessenberg $(N+1) \times (N+1)$ matrix over a field. Then the
Krylov matrix $K(H, e_0, N + 1)$ is nonsingular. -/
theorem IsUnreducedUpperHessenberg.isUnit_krylovMatrix (h : H.IsUnreducedUpperHessenberg) :
    IsUnit (krylovMatrix H (Pi.single 0 1) (N + 1)) :=
  (IsUpperTriangular.isUnit_iff
    h.1.isUpperTriangular_krylovMatrix).2 h.krylovMatrix_apply_self_ne_zero

/-- Let $H$ be an $(N+1) \times (N+1)$ matrix over a field. Then $H$ is unreduced upper Hessenberg
if and only if
$$K(H, e_0, N + 1) = [e_0 \mid H e_0 \mid \cdots \mid H^N e_0]$$
is upper triangular and has a nonzero determinant. This is Theorem 7.4.3 of [golub2013matrix]
for $Q = I$.

For the converse direction, write $H = (H K) K^{-1}$ with $K = K(H, e_0, N + 1)$. Column $l$ of
$H K$ is $H^{l+1} e_0$, which is zero below entry $l + 1$, and $K^{-1}$ is upper triangular; so
$H$ is upper Hessenberg. Then the recursion $K_{i+1,i+1} = h_{i+1,i} K_{ii}$ excludes a zero on
the subdiagonal. -/
theorem isUnreducedUpperHessenberg_iff_krylovMatrix :
    H.IsUnreducedUpperHessenberg ↔
      (krylovMatrix H (Pi.single 0 1) (N + 1)).IsUpperTriangular ∧
        IsUnit (krylovMatrix H (Pi.single 0 1) (N + 1)).det := by
  set Kr := krylovMatrix H (Pi.single 0 1) (N + 1) with hKr
  refine ⟨fun h => ⟨h.1.isUpperTriangular_krylovMatrix,
    (isUnit_iff_isUnit_det _).1 h.isUnit_krylovMatrix⟩, fun ⟨ht, hu⟩ => ?_⟩
  have hHK : ∀ (i : Fin (N + 1)) (l : Fin (N + 1)), (H * Kr) i l =
      (H ^ ((l : ℕ) + 1) *ᵥ Pi.single 0 1) i := fun i l =>
    congrFun (col_mul_krylovMatrix H (Pi.single 0 1) (N + 1) l) i
  have hHess : H.IsUpperHessenberg := by
    rw [isUpperHessenberg_iff_fin]
    intro i j hji
    rw [← mul_nonsing_inv_cancel_right Kr H hu, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases le_or_gt l j with hl | hl
    · have hl' : (l : ℕ) + 1 < N + 1 := by have : (l : ℕ) ≤ j := hl; omega
      have hz := ht (show (⟨(l : ℕ) + 1, hl'⟩ : Fin (N + 1)) < i from by
        rw [Fin.lt_def]; have : (l : ℕ) ≤ j := hl; simp only; omega)
      rw [hKr, krylovMatrix_apply] at hz
      rw [hHK]
      exact mul_eq_zero_of_left hz _
    · rw [ht.inv hl, mul_zero]
  refine (isUnreducedUpperHessenberg_iff_succ).2 ⟨hHess, fun i hi => ?_⟩
  have hdiag : Kr i.succ i.succ = 0 := by
    rw [hKr, hHess.krylovMatrix_succ_succ, hi, zero_mul]
  rw [det_of_isUpperTriangular ht, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff] at hu
  exact hu i.succ (Finset.mem_univ _) hdiag

/-- Let $A$ be an $(N+1) \times (N+1)$ matrix over a field with involution, and let $Q$ be a unitary
$(N+1) \times (N+1)$ matrix with first column $Q e_0$. Then $Q^H A Q$ is unreduced upper
Hessenberg if and only if
$$R = Q^H K(A, Q e_0, N + 1)$$
is upper triangular and has a nonzero determinant. This is Theorem 7.4.3 of [golub2013matrix]. -/
theorem isUnreducedUpperHessenberg_conj_iff_krylovMatrix [StarRing K]
    {Q : Matrix (Fin (N + 1)) (Fin (N + 1)) K} (hQ : Q ∈ unitaryGroup (Fin (N + 1)) K)
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) K) :
    (star Q * A * Q).IsUnreducedUpperHessenberg ↔
      (star Q * krylovMatrix A (Q.col 0) (N + 1)).IsUpperTriangular ∧
        IsUnit (star Q * krylovMatrix A (Q.col 0) (N + 1)).det := by
  rw [← mulVec_single_one, conjTranspose_mul_krylovMatrix hQ,
    isUnreducedUpperHessenberg_iff_krylovMatrix]

/-- Let $H$ be an unreduced upper Hessenberg matrix over a field, with a finite linearly ordered
index set, and let $R$ be an upper triangular matrix with no zero on its diagonal. Then
$R H R^{-1}$ is unreduced upper Hessenberg.

The product is upper Hessenberg by the rules for products of band matrices, and its subdiagonal
entry at $(i, j)$ is $r_{ii} h_{ij} r_{jj}^{-1}$. -/
theorem IsUnreducedUpperHessenberg.mul_mul_inv_of_isUpperTriangular {n : Type*} [Fintype n]
    [LinearOrder n] {H R : Matrix n n K} (h : H.IsUnreducedUpperHessenberg)
    (hR : R.IsUpperTriangular) (hdiag : ∀ i, R i i ≠ 0) :
    (R * H * R⁻¹).IsUnreducedUpperHessenberg := by
  have hRu : IsUnit R := (IsUpperTriangular.isUnit_iff hR).2 hdiag
  have hRi : R⁻¹.IsUpperTriangular := hR.inv
  refine ⟨(hR.mul_isUpperHessenberg h.1).mul_isUpperTriangular hRi, fun i j hij => ?_⟩
  have hinv : R⁻¹ j j * R j j = 1 := by
    rw [← hRi.mul_apply_self hR, nonsing_inv_mul R ((isUnit_iff_isUnit_det R).1 hRu), one_apply_eq]
  have hentry : (R * H * R⁻¹) i j = R i i * H i j * R⁻¹ j j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [Matrix.mul_apply, Finset.sum_eq_single i]
      · intro a _ ha
        rcases lt_or_gt_of_ne ha with ha | ha
        · rw [hR ha, zero_mul]
        · rw [h.1 a j ⟨i, hij.lt, ha⟩, mul_zero]
      · simp
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with hb | hb
      · rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
        intro a _
        rcases lt_or_ge a i with ha | ha
        · rw [hR ha, zero_mul]
        · rw [h.1 a b ⟨j, hb, lt_of_lt_of_le hij.lt ha⟩, mul_zero]
      · rw [hRi hb, mul_zero]
    · simp
  rw [hentry]
  refine mul_ne_zero (mul_ne_zero (hdiag i) (h.2 i j hij)) ?_
  exact left_ne_zero_of_mul_eq_one hinv

/-- **The implicit-shift principle** behind the Francis and QZ steps ([golub2013matrix], §7.5.5 and
§7.7.6). Let $H$ be an unreduced upper Hessenberg $(N+1) \times (N+1)$ matrix over a field with
involution, let $p$ be a polynomial, and let $Z$ be a unitary $(N+1) \times (N+1)$ matrix such
that $Z^H H Z$ is upper Hessenberg and the first column $Z e_0$ is a multiple of $p(H) e_0$.
Then $Z^H p(H)$ is upper triangular.

Let $K = K(H, e_0, N + 1)$, which is upper triangular and nonsingular, and let
$p(H) e_0 = c Z e_0$. Then $Z^H p(H) K = Z^H K(H, p(H) e_0, N + 1) = c K(Z^H H Z, e_0, N + 1)$
is upper triangular, and so is $K^{-1}$. In the Lean statement the condition on $Z e_0$ is the
membership of `Z.col 0` in the span of $p(H) e_0$. -/
theorem IsUnreducedUpperHessenberg.isUpperTriangular_star_mul_aeval [StarRing K]
    (h : H.IsUnreducedUpperHessenberg) (p : K[X]) {Z : Matrix (Fin (N + 1)) (Fin (N + 1)) K}
    (hZ : Z ∈ unitaryGroup (Fin (N + 1)) K) (hG : (star Z * H * Z).IsUpperHessenberg)
    (hcol : Z.col 0 ∈ Submodule.span K {aeval H p *ᵥ Pi.single 0 1}) :
    (star Z * aeval H p).IsUpperTriangular := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hcol
  have hZ0 : Z *ᵥ Pi.single 0 1 ≠ 0 := by
    intro h0
    have h1 : star Z *ᵥ (Z *ᵥ Pi.single (0 : Fin (N + 1)) (1 : K)) = Pi.single 0 1 := by
      rw [mulVec_mulVec, (mem_unitaryGroup_iff').1 hZ, one_mulVec]
    rw [h0, mulVec_zero] at h1
    simpa using congrFun h1 0
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul, ← mulVec_single_one] at hc
    exact hZ0 hc.symm
  have hp : aeval H p *ᵥ Pi.single 0 1 = c⁻¹ • (Z *ᵥ Pi.single 0 1) := by
    rw [mulVec_single_one Z, ← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  set Kr := krylovMatrix H (Pi.single 0 1) (N + 1)
  have hKu : IsUnit Kr.det := (isUnit_iff_isUnit_det _).1 h.isUnit_krylovMatrix
  have hprod : star Z * aeval H p * Kr =
      c⁻¹ • krylovMatrix (star Z * H * Z) (Pi.single 0 1) (N + 1) := by
    rw [Matrix.mul_assoc, aeval_mul_krylovMatrix, hp, krylovMatrix_smul, Matrix.mul_smul,
      conjTranspose_mul_krylovMatrix hZ]
  rw [← mul_nonsing_inv_cancel_right Kr (star Z * aeval H p) hKu, hprod]
  refine BlockTriangular.mul ?_ (IsUpperTriangular.inv
    h.1.isUpperTriangular_krylovMatrix)
  intro i j hji
  rw [Matrix.smul_apply, hG.isUpperTriangular_krylovMatrix hji, smul_zero]

end HessenbergKrylov

end Matrix
