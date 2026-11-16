/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix`, beside `Mathlib.LinearAlgebra.Matrix.Circulant`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.LinearAlgebra.Matrix.Permutation
import Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz

/-!
# Toeplitz, Hankel and persymmetric matrices

This file studies square and rectangular matrices on `Fin n` that are constant along diagonals,
constant along antidiagonals, or symmetric about the antidiagonal, following [golub2013matrix] §4.7,
§4.8.2 and §12.1.7. Indices run from $0$ to $n - 1$, and $\bar{\imath} = n - 1 - i$ is the reversal
of the index $i$. A **Toeplitz matrix** has entries $a_{ij} = r_{j-i}$ for a two-sided sequence $r$,
a **Hankel matrix** has entries $a_{ij} = h_{i+j}$, and a square matrix $A$ is **persymmetric** if
$a_{\bar{\jmath}\bar{\imath}} = a_{ij}$ for all $i, j$. With the exchange matrix $\mathcal{E}_n$,
which has ones on the antidiagonal, persymmetry is $\mathcal{E}_n A \mathcal{E}_n = A^T$.

A square Toeplitz matrix is persymmetric, and the inverse of a persymmetric matrix is persymmetric.
The symmetric Toeplitz matrices $T_n = (r_{|i-j|})$ of the Levinson–Durbin–Trench theory are nested,
$T_k$ is the leading block of $T_n$, and they satisfy the bordering identity
$$T_{k+1} = \begin{bmatrix} T_k & \mathcal{E}_k r \\ r^T \mathcal{E}_k & r_0 \end{bmatrix}, \qquad
  r = (r_1, \dots, r_k)^T.$$
Reversing the rows of a Hankel matrix gives a Toeplitz matrix. A circulant matrix is a Toeplitz
matrix with wraparound and a polynomial in the downshift $\mathcal{D}_n$.

## Main definitions

* `Matrix.IsPersymmetric`: $A$ is symmetric about the antidiagonal,
  $a_{\bar{\jmath}\bar{\imath}} = a_{ij}$.
* `Matrix.toeplitz`: the $m \times n$ Toeplitz matrix $(r_{j-i})$ of a sequence
  $r : \mathbb{Z} \to R$.
* `Matrix.IsToeplitz`: $A$ is a Toeplitz matrix, that is, constant along each diagonal.
* `Matrix.symmToeplitz`: the $n \times n$ symmetric Toeplitz matrix $(r_{|i-j|})$ of a sequence
  $r : \mathbb{N} \to R$.
* `Matrix.hankel`: the $m \times n$ Hankel matrix $(h_{i+j})$ of a sequence $h : \mathbb{N} \to R$.
* `Matrix.IsHankel`: $A$ is a Hankel matrix, that is, constant along each antidiagonal.

## Main results

* `Matrix.isPersymmetric_iff_submatrix_rev`, `Matrix.isPersymmetric_iff_exchange_mul_mul_exchange`:
  $A$ is persymmetric if and only if reversing its rows and columns gives $A^T$, that is,
  $\mathcal{E}_n A \mathcal{E}_n = A^T$.
* `Matrix.isPersymmetric_iff_isSymm_exchange_mul`: $A$ is persymmetric if and only if
  $\mathcal{E}_n A$ is symmetric.
* `Matrix.IsPersymmetric.inv`: the inverse of a persymmetric matrix is persymmetric.
* `Matrix.isToeplitz_iff`: a matrix is Toeplitz if and only if entries with the same offset $j - i$
  are equal.
* `Matrix.IsToeplitz.isPersymmetric`: a square Toeplitz matrix is persymmetric.
* `Matrix.symmTridiagonalToeplitz_eq_toeplitz`, `Matrix.tridiagonalToeplitz_eq_toeplitz`: the
  tridiagonal Toeplitz matrices of `Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz` are Toeplitz
  matrices.
* `Matrix.leadingPrincipal_symmToeplitz`: the leading $k \times k$ block of $T_n$ is $T_k$.
* `Matrix.symmToeplitz_succ_eq_fromBlocks`: the bordering identity for $T_{k+1}$.
* `Matrix.exchange_mul_symmToeplitz`, `Matrix.inv_symmToeplitz_mul_exchange`: $T_n$ and $T_n^{-1}$
  commute with $\mathcal{E}_n$.
* `Matrix.isHankel_iff`: a matrix is Hankel if and only if entries with the same index sum $i + j$
  are equal.
* `Matrix.IsHankel.isToeplitz_submatrix_rev`, `Matrix.IsHankel.isToeplitz_exchange_mul`: for a
  Hankel matrix $H$, the matrix $\mathcal{E}_m H$ is Toeplitz.
* `Matrix.isToeplitz_circulant`: a circulant matrix is Toeplitz.
* `Matrix.circulant_eq_sum_downshift_pow`: a circulant matrix is a polynomial in the downshift.
* `Matrix.secondDifferencePeriodic_eq_circulant`: for $n \ge 3$ the periodic second difference
  matrix is a circulant matrix.

## Notation

* $\mathcal{E}_n$: the exchange matrix `Matrix.exchange n`.
* $\mathcal{D}_n$: the downshift matrix `Matrix.downshift n`.

## Implementation notes

* All matrices are indexed by `Fin n`, and all statements are entrywise.
* The Toeplitz matrix is rectangular and takes a sequence indexed by `ℤ`. An unsymmetric Toeplitz
  matrix, with $r_{j-i}$ above the diagonal and $p_{i-j}$ below it as in [golub2013matrix] §4.7.8,
  therefore needs no second definition.
* [golub2013matrix] states persymmetry and the relation between Hankel and Toeplitz matrices with
  the exchange matrix: $\mathcal{E} A \mathcal{E} = A^T$, and "$\mathcal{E} H$ is Toeplitz". Here
  they are first stated with the reversal `Fin.rev` of rows and columns, and then with
  `Matrix.exchange` and `Matrix.downshift` from `Numlib.LinearAlgebra.Matrix.Permutation`. The link
  is `Matrix.exchange_mul_mul_exchange_eq_submatrix`: $\mathcal{E}_n A \mathcal{E}_n$ is
  `A.submatrix Fin.rev Fin.rev`.
* The diagonalization of a circulant matrix by the discrete Fourier transform is in
  `Numlib.Analysis.Fourier.Circulant`. This module, and the displacement and Levinson theories built
  on it, do not depend on the discrete Fourier transform.
-/

open scoped Fin.IntCast Fin.CommRing

namespace Matrix

variable {R : Type*} {m n : ℕ}

/-! ### Persymmetry -/

/-- A square matrix $A$ of order $n$ is **persymmetric** if it is symmetric about the antidiagonal:
$$a_{\bar{\jmath}\bar{\imath}} = a_{ij} \quad \text{for all } i, j,$$
where $\bar{\imath} = n - 1 - i$. This is §4.7.1 of [golub2013matrix].

The reversal $\bar{\imath}$ is `Fin.rev i`. The definition $\mathcal{E}_n A \mathcal{E}_n = A^T$
of [golub2013matrix] is `Matrix.isPersymmetric_iff_exchange_mul_mul_exchange`. -/
def IsPersymmetric (A : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j, A (Fin.rev j) (Fin.rev i) = A i j

/-- A square matrix $A$ is persymmetric if and only if reversing the order of its rows and columns
gives its transpose: $(a_{\bar{\imath}\bar{\jmath}})_{ij} = A^T$.

This is the condition $\mathcal{E}_n A \mathcal{E}_n = A^T$ of [golub2013matrix] §4.7.1, written
without the permutation matrices. -/
theorem isPersymmetric_iff_submatrix_rev {A : Matrix (Fin n) (Fin n) R} :
    A.IsPersymmetric ↔ A.submatrix Fin.rev Fin.rev = Aᵀ := by
  constructor
  · intro h
    ext i j
    exact h j i
  · intro h i j
    exact congrFun (congrFun h j) i

/-- Let $A$ be a persymmetric matrix over a commutative ring. Then $A^{-1}$ is persymmetric. This is
§4.7.1 of [golub2013matrix]:
$$\mathcal{E} A^{-1} \mathcal{E} = (\mathcal{E} A \mathcal{E})^{-1} = (A^T)^{-1} = (A^{-1})^T.$$

The inverse is Mathlib's `Matrix.inv`, so the statement also holds for a singular $A$, whose
inverse is $0$. -/
theorem IsPersymmetric.inv [CommRing R] {A : Matrix (Fin n) (Fin n) R}
    (hA : A.IsPersymmetric) : A⁻¹.IsPersymmetric := by
  rw [isPersymmetric_iff_submatrix_rev] at hA ⊢
  have h : (A.submatrix Fin.rev Fin.rev)⁻¹ = A⁻¹.submatrix Fin.rev Fin.rev :=
    inv_submatrix_equiv A Fin.revPerm Fin.revPerm
  rw [← h, hA, transpose_nonsing_inv]

section Exchange

variable [NonAssocSemiring R]

/-- A square matrix $A$ of order $n$ is persymmetric if and only if
$$\mathcal{E}_n A \mathcal{E}_n = A^T.$$
This is the definition of persymmetry in [golub2013matrix] §4.7.1. -/
theorem isPersymmetric_iff_exchange_mul_mul_exchange {A : Matrix (Fin n) (Fin n) R} :
    A.IsPersymmetric ↔ exchange n * A * exchange n = Aᵀ := by
  rw [exchange_mul_mul_exchange_eq_submatrix, isPersymmetric_iff_submatrix_rev]

/-- A square matrix $A$ of order $n$ is persymmetric if and only if $\mathcal{E}_n A$ is symmetric.
-/
theorem isPersymmetric_iff_isSymm_exchange_mul {A : Matrix (Fin n) (Fin n) R} :
    A.IsPersymmetric ↔ (exchange n * A).IsSymm := by
  rw [exchange_mul_eq_submatrix, IsSymm, ← Matrix.ext_iff]
  constructor
  · intro h i j
    simpa using h (Fin.rev i) j
  · intro h i j
    simpa using h (Fin.rev i) j

/-- If $A$ is persymmetric of order $n$, then $\mathcal{E}_n A$ is symmetric. This is §4.7.1 of
[golub2013matrix]. -/
theorem IsPersymmetric.isSymm_exchange_mul {A : Matrix (Fin n) (Fin n) R}
    (hA : A.IsPersymmetric) : (exchange n * A).IsSymm :=
  isPersymmetric_iff_isSymm_exchange_mul.mp hA

end Exchange

/-- If $A$ is symmetric and persymmetric of order $n$, then $A$ commutes with the exchange matrix:
$\mathcal{E}_n A = A \mathcal{E}_n$. -/
theorem IsPersymmetric.exchange_mul_eq_mul_exchange [Semiring R] {A : Matrix (Fin n) (Fin n) R}
    (hA : A.IsPersymmetric) (hS : A.IsSymm) : exchange n * A = A * exchange n := by
  have h := isPersymmetric_iff_exchange_mul_mul_exchange.mp hA
  rw [hS.eq] at h
  calc exchange n * A = exchange n * A * exchange n * exchange n := by
        rw [Matrix.mul_assoc (exchange n * A), exchange_mul_exchange, Matrix.mul_one]
    _ = A * exchange n := by rw [h]

/-! ### Toeplitz matrices -/

/-- The $m \times n$ **Toeplitz matrix** of a two-sided sequence $r : \mathbb{Z} \to R$ has the
entries
$$a_{ij} = r_{j-i}.$$
This is the Toeplitz matrix of [golub2013matrix] §4.7. -/
def toeplitz (r : ℤ → R) : Matrix (Fin m) (Fin n) R :=
  of fun (i : Fin m) (j : Fin n) => r ((j : ℤ) - i)

/-- The entry $(i, j)$ of `Matrix.toeplitz r` is $r_{j-i}$. -/
theorem toeplitz_apply (r : ℤ → R) (i : Fin m) (j : Fin n) :
    (toeplitz r : Matrix (Fin m) (Fin n) R) i j = r ((j : ℤ) - i) := rfl

/-- An $m \times n$ matrix $A$ **is Toeplitz** if $A$ is the Toeplitz matrix $(r_{j-i})$ of some
sequence $r : \mathbb{Z} \to R$. -/
def IsToeplitz (A : Matrix (Fin m) (Fin n) R) : Prop :=
  ∃ r : ℤ → R, A = toeplitz r

/-- An $m \times n$ matrix $A$ is Toeplitz if and only if it is constant along each diagonal:
$a_{ij} = a_{kl}$ whenever $j - i = l - k$. -/
theorem isToeplitz_iff [Zero R] {A : Matrix (Fin m) (Fin n) R} :
    A.IsToeplitz ↔ ∀ (i : Fin m) (j : Fin n) (k : Fin m) (l : Fin n),
      (j : ℤ) - i = (l : ℤ) - k → A i j = A k l := by
  classical
  constructor
  · rintro ⟨r, rfl⟩ i j k l h
    rw [toeplitz_apply, toeplitz_apply, h]
  · intro hA
    refine ⟨fun d => if h : ∃ p : Fin m × Fin n, (p.2 : ℤ) - p.1 = d then
      A h.choose.1 h.choose.2 else 0, ?_⟩
    ext i j
    have hex : ∃ p : Fin m × Fin n, (p.2 : ℤ) - p.1 = (j : ℤ) - i := ⟨(i, j), rfl⟩
    rw [toeplitz_apply, dite_eq_left hex]
    exact hA _ _ _ _ hex.choose_spec.symm

/-- A square Toeplitz matrix is persymmetric, because the entry $(\bar{\jmath}, \bar{\imath})$ has
the same offset $\bar{\imath} - \bar{\jmath} = j - i$ as the entry $(i, j)$. -/
theorem IsToeplitz.isPersymmetric {A : Matrix (Fin n) (Fin n) R} (hA : A.IsToeplitz) :
    A.IsPersymmetric := by
  obtain ⟨r, rfl⟩ := hA
  intro i j
  rw [toeplitz_apply, toeplitz_apply, Fin.val_rev, Fin.val_rev]
  congr 1
  omega

/-- The symmetric tridiagonal Toeplitz matrix $\operatorname{tridiag}(a, b, a)$ of order $n$,
`Matrix.symmTridiagonalToeplitz n a b`, is the Toeplitz matrix of the sequence $r$ with
$r_0 = b$, $r_{\pm 1} = a$, and $r_d = 0$ for $|d| \ge 2$. -/
theorem symmTridiagonalToeplitz_eq_toeplitz (n : ℕ) (a b : ℝ) :
    symmTridiagonalToeplitz n a b
      = toeplitz fun d : ℤ => if d = 0 then b else if |d| = 1 then a else 0 := by
  ext i j
  rw [symmTridiagonalToeplitz_apply', toeplitz_apply]
  simp only [abs_eq (zero_le_one' ℤ)]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- The tridiagonal Toeplitz matrix $\operatorname{tridiag}(a, b, c)$ of order $n$, with subdiagonal
$a$, diagonal $b$ and superdiagonal $c$, is the Toeplitz matrix of the sequence $r$ with
$r_{-1} = a$, $r_0 = b$, $r_1 = c$, and $r_d = 0$ for $|d| \ge 2$.

The matrix is `Matrix.tridiagonalToeplitz n a b c`. -/
theorem tridiagonalToeplitz_eq_toeplitz (n : ℕ) (a b c : ℝ) :
    tridiagonalToeplitz n a b c
      = toeplitz fun d : ℤ =>
        if d = 0 then b else if d = -1 then a else if d = 1 then c else 0 := by
  ext i j
  rw [tridiagonalToeplitz_apply, toeplitz_apply]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- The transpose of the $m \times n$ Toeplitz matrix of $\rho$ is the $n \times m$ Toeplitz matrix
of the reflected sequence $d \mapsto \rho_{-d}$. -/
theorem transpose_toeplitz (ρ : ℤ → R) :
    (toeplitz ρ : Matrix (Fin m) (Fin n) R)ᵀ = toeplitz fun d => ρ (-d) := by
  ext i j
  simp only [transpose_apply, toeplitz_apply, neg_sub]

/-- Let $T$ be the $n \times n$ Toeplitz matrix of $\rho$, and let $v$ be a sequence indexed by
$\mathbb{N}$. Then
$$(T v)_i = \sum_{j=0}^{n-1} \rho_{j-i} v_j,$$
where $T$ acts on the vector $(v_0, \dots, v_{n-1})$. -/
theorem toeplitz_mulVec_apply [NonUnitalNonAssocSemiring R] (ρ : ℤ → R) (v : ℕ → R)
    (i : Fin n) :
    ((toeplitz ρ : Matrix (Fin n) (Fin n) R) *ᵥ fun j : Fin n => v j) i =
      ∑ j ∈ Finset.range n, ρ ((j : ℤ) - i) * v j := by
  simp only [mulVec, dotProduct, toeplitz_apply]
  exact Fin.sum_univ_eq_sum_range (fun j => ρ ((j : ℤ) - (i : ℕ)) * v j) n

/-- The symmetric tridiagonal Toeplitz matrix `Matrix.symmTridiagonalToeplitz n a b` is Toeplitz. -/
theorem isToeplitz_symmTridiagonalToeplitz (n : ℕ) (a b : ℝ) :
    (symmTridiagonalToeplitz n a b).IsToeplitz :=
  ⟨_, symmTridiagonalToeplitz_eq_toeplitz n a b⟩

/-- The tridiagonal Toeplitz matrix `Matrix.tridiagonalToeplitz n a b c` is Toeplitz. -/
theorem isToeplitz_tridiagonalToeplitz (n : ℕ) (a b c : ℝ) :
    (tridiagonalToeplitz n a b c).IsToeplitz :=
  ⟨_, tridiagonalToeplitz_eq_toeplitz n a b c⟩

/-! ### Symmetric Toeplitz matrices -/

/-- The $n \times n$ **symmetric Toeplitz matrix** of a sequence $r : \mathbb{N} \to R$ has the
entries
$$t_{ij} = r_{|i-j|}.$$
This is the matrix $T_n$ of [golub2013matrix] §4.7.2, where $r_0 = 1$. Here $r_0$ is arbitrary. -/
def symmToeplitz (n : ℕ) (r : ℕ → R) : Matrix (Fin n) (Fin n) R :=
  of fun (i j : Fin n) => r ((i : ℤ) - j).natAbs

/-- The entry $(i, j)$ of `Matrix.symmToeplitz n r` is $r_{|i-j|}$. -/
theorem symmToeplitz_apply (r : ℕ → R) (i j : Fin n) :
    symmToeplitz n r i j = r ((i : ℤ) - j).natAbs := rfl

/-- The symmetric Toeplitz matrix of $r$ is the Toeplitz matrix of the even sequence
$d \mapsto r_{|d|}$. -/
theorem symmToeplitz_eq_toeplitz (n : ℕ) (r : ℕ → R) :
    symmToeplitz n r = toeplitz fun d => r d.natAbs := by
  ext i j
  rw [symmToeplitz_apply, toeplitz_apply, ← Int.natAbs_neg, neg_sub]

/-- Let $T_n$ be the symmetric Toeplitz matrix of $r$, and let $v$ be a sequence indexed by
$\mathbb{N}$. Then
$$(T_n v)_i = \sum_{j=0}^{n-1} r_{|i-j|} v_j,$$
where $T_n$ acts on the vector $(v_0, \dots, v_{n-1})$. -/
theorem symmToeplitz_mulVec_apply [NonUnitalNonAssocSemiring R] (r : ℕ → R) (v : ℕ → R)
    (i : Fin n) :
    (symmToeplitz n r *ᵥ fun j : Fin n => v j) i =
      ∑ j ∈ Finset.range n, r ((i : ℤ) - j).natAbs * v j := by
  simp only [mulVec, dotProduct, symmToeplitz_apply]
  exact Fin.sum_univ_eq_sum_range (fun j => r (((i : ℕ) : ℤ) - j).natAbs * v j) n

/-- A symmetric Toeplitz matrix is symmetric. -/
theorem isSymm_symmToeplitz (n : ℕ) (r : ℕ → R) : (symmToeplitz n r).IsSymm := by
  ext i j
  rw [transpose_apply, symmToeplitz_apply, symmToeplitz_apply, ← Int.natAbs_neg, neg_sub]

/-- A symmetric Toeplitz matrix is Toeplitz. -/
theorem isToeplitz_symmToeplitz (n : ℕ) (r : ℕ → R) : (symmToeplitz n r).IsToeplitz :=
  ⟨_, symmToeplitz_eq_toeplitz n r⟩

/-- A symmetric Toeplitz matrix is persymmetric. -/
theorem isPersymmetric_symmToeplitz (n : ℕ) (r : ℕ → R) : (symmToeplitz n r).IsPersymmetric :=
  (isToeplitz_symmToeplitz n r).isPersymmetric

/-- A symmetric Toeplitz matrix $T_n$ is unchanged when the order of its rows and columns is
reversed. This is $\mathcal{E}_n T_n \mathcal{E}_n = T_n$ of [golub2013matrix] §4.7.3, which
with $\mathcal{E}_n^2 = I$ is $\mathcal{E}_n T_n = T_n \mathcal{E}_n$. -/
theorem symmToeplitz_submatrix_rev (n : ℕ) (r : ℕ → R) :
    (symmToeplitz n r).submatrix Fin.rev Fin.rev = symmToeplitz n r := by
  rw [isPersymmetric_iff_submatrix_rev.mp (isPersymmetric_symmToeplitz n r), isSymm_symmToeplitz]

/-- **Nesting of the symmetric Toeplitz matrices.** For $k \le n$, the leading $k \times k$ block of
$T_n$ is $T_k$. This is §4.7.2 of [golub2013matrix]. -/
theorem leadingPrincipal_symmToeplitz {k : ℕ} (h : k ≤ n) (r : ℕ → R) :
    (symmToeplitz n r).submatrix (Fin.castLE h) (Fin.castLE h) = symmToeplitz k r := by
  ext i j
  rfl

/-- A symmetric Toeplitz matrix commutes with the exchange matrix:
$$\mathcal{E}_n T_n = T_n \mathcal{E}_n.$$
This is §4.7.3 of [golub2013matrix]. -/
theorem exchange_mul_symmToeplitz [Semiring R] (n : ℕ) (r : ℕ → R) :
    exchange n * symmToeplitz n r = symmToeplitz n r * exchange n :=
  (isPersymmetric_symmToeplitz n r).exchange_mul_eq_mul_exchange (isSymm_symmToeplitz n r)

/-- Over a commutative ring, the inverse of a symmetric Toeplitz matrix commutes with the exchange
matrix: $T_n^{-1} \mathcal{E}_n = \mathcal{E}_n T_n^{-1}$. This is §4.7.3 of [golub2013matrix].

The inverse is Mathlib's `Matrix.inv`, so the statement also holds for a singular $T_n$, whose
inverse is $0$. -/
theorem inv_symmToeplitz_mul_exchange [CommRing R] (n : ℕ) (r : ℕ → R) :
    (symmToeplitz n r)⁻¹ * exchange n = exchange n * (symmToeplitz n r)⁻¹ :=
  ((isPersymmetric_symmToeplitz n r).inv.exchange_mul_eq_mul_exchange
    (by rw [IsSymm, transpose_nonsing_inv, (isSymm_symmToeplitz n r).eq])).symm

/-- **Bordering of the symmetric Toeplitz matrices.** Let $\rho : \mathbb{N} \to R$, let $T_k$ be
the symmetric Toeplitz matrix of $\rho$ of order $k$, and let $r = (\rho_1, \dots, \rho_k)^T$.
Then
$$T_{k+1} = \begin{bmatrix} T_k & \mathcal{E}_k r \\ r^T \mathcal{E}_k & \rho_0 \end{bmatrix}.$$
This is §4.7.3 of [golub2013matrix].

The blocks are glued along `finSumFinEquiv : Fin k ⊕ Fin 1 ≃ Fin (k + 1)`. The column
$\mathcal{E}_k r$ is a `Matrix.replicateCol`, and the row $r^T \mathcal{E}_k$ is a
`Matrix.replicateRow`. -/
theorem symmToeplitz_succ_eq_fromBlocks [NonAssocSemiring R] (k : ℕ) (ρ : ℕ → R) :
    symmToeplitz (k + 1) ρ =
      (fromBlocks (symmToeplitz k ρ)
        (replicateCol (Fin 1) (exchange k *ᵥ fun i : Fin k => ρ (i + 1)))
        (replicateRow (Fin 1) ((fun i : Fin k => ρ (i + 1)) ᵥ* exchange k))
        (of fun _ _ => ρ 0)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [symmToeplitz_apply]
    | cast b =>
      simp only [submatrix_apply, finSumFinEquiv_symm_last, finSumFinEquiv_symm_apply_castSucc,
        fromBlocks_apply₂₁, replicateRow_apply, vecMul_exchange_apply, symmToeplitz_apply,
        Fin.val_last, Fin.val_castSucc, Fin.val_rev]
      congr 1
      omega
  | cast a =>
    induction j using Fin.lastCases with
    | last =>
      simp only [submatrix_apply, finSumFinEquiv_symm_last, finSumFinEquiv_symm_apply_castSucc,
        fromBlocks_apply₁₂, replicateCol_apply, exchange_mulVec_apply, symmToeplitz_apply,
        Fin.val_last, Fin.val_castSucc, Fin.val_rev]
      congr 1
      omega
    | cast b =>
      simp [symmToeplitz_apply]

/-! ### Hankel matrices -/

/-- The $m \times n$ **Hankel matrix** of a sequence $h : \mathbb{N} \to R$ has the entries
$$a_{ij} = h_{i+j},$$
so it is constant along each antidiagonal. This is the Hankel matrix of [golub2013matrix]
§12.1.7. -/
def hankel (h : ℕ → R) : Matrix (Fin m) (Fin n) R :=
  of fun (i : Fin m) (j : Fin n) => h (i + j)

/-- The entry $(i, j)$ of `Matrix.hankel h` is $h_{i+j}$. -/
theorem hankel_apply (h : ℕ → R) (i : Fin m) (j : Fin n) :
    (hankel h : Matrix (Fin m) (Fin n) R) i j = h (i + j) := rfl

/-- An $m \times n$ matrix $A$ **is Hankel** if $A$ is the Hankel matrix $(h_{i+j})$ of some
sequence $h : \mathbb{N} \to R$. -/
def IsHankel (A : Matrix (Fin m) (Fin n) R) : Prop :=
  ∃ h : ℕ → R, A = hankel h

/-- An $m \times n$ matrix $A$ is Hankel if and only if it is constant along each antidiagonal:
$a_{ij} = a_{kl}$ whenever $i + j = k + l$. This is the counterpart of `Matrix.isToeplitz_iff`. -/
theorem isHankel_iff [Zero R] {A : Matrix (Fin m) (Fin n) R} :
    A.IsHankel ↔ ∀ (i : Fin m) (j : Fin n) (k : Fin m) (l : Fin n),
      (i : ℕ) + j = k + l → A i j = A k l := by
  classical
  constructor
  · rintro ⟨h, rfl⟩ i j k l hs
    rw [hankel_apply, hankel_apply, hs]
  · intro hA
    refine ⟨fun d => if h : ∃ p : Fin m × Fin n, (p.1 : ℕ) + p.2 = d then
      A h.choose.1 h.choose.2 else 0, ?_⟩
    ext i j
    have hex : ∃ p : Fin m × Fin n, (p.1 : ℕ) + p.2 = (i : ℕ) + j := ⟨(i, j), rfl⟩
    rw [hankel_apply, dite_eq_left hex]
    exact hA _ _ _ _ hex.choose_spec.symm

/-- If $A$ is an $m \times n$ Hankel matrix, then reversing the order of its rows gives a Toeplitz
matrix: the entry $(i, j)$ of the result is $h_{m-1-i+j}$, which depends only on $j - i$. This
is the statement "$\mathcal{E}_m H$ is Toeplitz" of [golub2013matrix] §12.1.7, written without
the permutation matrix. -/
theorem IsHankel.isToeplitz_submatrix_rev {A : Matrix (Fin m) (Fin n) R} (hA : A.IsHankel) :
    (A.submatrix Fin.rev id).IsToeplitz := by
  obtain ⟨h, rfl⟩ := hA
  refine ⟨fun d => h ((m - 1 : ℤ) + d).toNat, ?_⟩
  ext i j
  rw [submatrix_apply, hankel_apply, toeplitz_apply, Fin.val_rev, id]
  congr 1
  omega

/-- If $H$ is an $m \times n$ Hankel matrix, then $\mathcal{E}_m H$ is Toeplitz. This is §12.1.7 of
[golub2013matrix]. -/
theorem IsHankel.isToeplitz_exchange_mul [NonAssocSemiring R] {A : Matrix (Fin m) (Fin n) R}
    (hA : A.IsHankel) : (exchange m * A).IsToeplitz := by
  rw [exchange_mul_eq_submatrix]
  exact hA.isToeplitz_submatrix_rev

/-! ### Circulant matrices -/

/-- A **circulant matrix is a Toeplitz matrix with wraparound**. Mathlib's circulant matrix
`Matrix.circulant v` of $v : \mathbb{Z}/n \to R$ has the entries $v_{i-j}$, with the subtraction
modulo $n$. It is the Toeplitz matrix of the sequence $d \mapsto v_{-d \bmod n}$. This is §4.8.2
of [golub2013matrix]. -/
theorem isToeplitz_circulant [Zero R] (v : Fin n → R) : (circulant v).IsToeplitz := by
  rcases n with _ | n
  · exact ⟨0, by ext i; exact i.elim0⟩
  · refine ⟨fun d => v ((-d : ℤ) : Fin (n + 1)), ?_⟩
    ext i j
    rw [circulant_apply, toeplitz_apply]
    congr 1
    push_cast
    simp

/-- A **circulant matrix is a polynomial in the downshift**. For $n \ge 1$ and
$z = (z_0, \dots, z_{n-1})$,
$$\operatorname{circ}(z) = \sum_{k=0}^{n-1} z_k \mathcal{D}_n^k.$$
This is (4.8.3) of [golub2013matrix].

The circulant matrix $\operatorname{circ}(z)$ is Mathlib's `Matrix.circulant z`, and the
hypothesis $n \ge 1$ is `[NeZero n]`. -/
theorem circulant_eq_sum_downshift_pow [Semiring R] [NeZero n] (z : Fin n → R) :
    circulant z = ∑ k : Fin n, z k • (downshift n : Matrix (Fin n) (Fin n) R) ^ (k : ℕ) := by
  ext i j
  simp only [downshift_pow, Fin.cast_val_eq_self, Matrix.sum_apply, Matrix.smul_apply,
    circulant_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

/-- For $i, j$ in `Fin n`, the value of $i - j$ is $i - j$ if $j \le i$, and $n + i - j$ otherwise.
-/
private theorem val_sub_fin (i j : Fin n) :
    ((i - j : Fin n) : ℕ) = if (j : ℕ) ≤ i then (i : ℕ) - j else n + i - j := by
  split_ifs with h
  · exact Fin.coe_sub_iff_le.mpr h
  · exact Fin.coe_sub_iff_lt.mpr (by omega)

/-- **The periodic second difference matrix is a circulant matrix.** For $n \ge 3$, the periodic
second difference matrix $\mathcal{T}^{(P)}_n$ is the circulant matrix with the first column
$(2, -1, 0, \dots, 0, -1)$. This is §4.8.6 of [golub2013matrix].

The hypothesis $n \ge 3$ is necessary. For $n = 2$ the two corner corrections fall on the
off-diagonal entries, and $\mathcal{T}^{(P)}_2 = \begin{bmatrix} 2 & -2 \\ -2 & 2 \end{bmatrix}$
is not this circulant matrix. The matrix $\mathcal{T}^{(P)}_n$ is
`Matrix.secondDifferencePeriodic n`. -/
theorem secondDifferencePeriodic_eq_circulant (hn : 3 ≤ n) :
    secondDifferencePeriodic n = circulant fun k : Fin n =>
      if (k : ℕ) = 0 then 2 else if (k : ℕ) = 1 ∨ (k : ℕ) + 1 = n then -1 else 0 := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  rw [secondDifferencePeriodic, Matrix.sub_apply, of_apply, symmTridiagonalToeplitz_apply',
    circulant_apply, val_sub_fin]
  split_ifs <;> first | (exfalso; omega) | ring

end Matrix
