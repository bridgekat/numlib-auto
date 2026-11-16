/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix`, beside `Mathlib.Data.Matrix.Composition`.
-/
import Mathlib.Data.Matrix.Composition
import Mathlib.RingTheory.Nilpotent.Basic
import Numlib.Analysis.Matrix.OperatorNorm
import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.LinearAlgebra.Matrix.LU

/-!
# Block tridiagonal matrices and their block LU factorization

A block tridiagonal matrix with $q \times q$ blocks ([golub2013matrix], §4.5.1–4.5.2;
[higham2002accuracy], §13.2) has diagonal blocks $D_0, \dots, D_N$, subdiagonal blocks
$E_0, \dots, E_{N-1}$ and superdiagonal blocks $F_0, \dots, F_{N-1}$. Write
$\operatorname{tridiag}(E, D, F)$ for it, with $E_i$ in block position $(i + 1, i)$ and $F_i$ in
block position $(i, i + 1)$. It is the scalar tridiagonal matrix `Matrix.tridiagonalOf E D F` of
`Numlib.LinearAlgebra.Matrix.Hessenberg` over the ring of $q \times q$ matrices, and the matrix that
the source writes is its flattening to a matrix of order $(N + 1)q$.

The block LU factorization is a recurrence in a noncommutative ring. The pivots are $U_0 = D_0$ and
$U_{i+1} = D_{i+1} - E_i U_i^{-1} F_i$, the multipliers are $L_i = E_i U_i^{-1}$, and when
$U_0, \dots, U_{N-1}$ are invertible, $\operatorname{tridiag}(E, D, F) = \operatorname{tridiag}(L,
I, 0) \operatorname{tridiag}(0, U, F)$. Strict block column diagonal dominance in the norm
$\|\cdot\|_1$ makes all pivots invertible and the multipliers contractive, bounds the pivots by the
matrix, and makes the matrix nonsingular. A block Cholesky factorization with given factors is also
proved.

## Main definitions

* `Matrix.blockTridiagonal`: the flattened block tridiagonal matrix
  $\operatorname{tridiag}(E, D, F)$.
* `Matrix.tridiagonalLUPivot`, `Matrix.tridiagonalLUMultiplier`: the pivots $U_i$ and the
  multipliers $L_i$ of the block LU recurrence.
* `Matrix.IsStrictBlockColDiagDominant`: strict block column diagonal dominance in the norm
  $\|\cdot\|_1$.
* `Matrix.blockColOffNorm`: the sum $\|F_{i-1}\|_1 + \|E_i\|_1$ of the norms of the off-diagonal
  blocks of block column $i$.

## Main results

* `Matrix.tridiagonalOf_eq_mul_of_isUnit_tridiagonalLUPivot`: if $U_0, \dots, U_{N-1}$ are units,
  then $\operatorname{tridiag}(E, D, F) = \operatorname{tridiag}(L, I, 0) \operatorname{tridiag}(0,
  U, F)$, over any ring.
* `Matrix.tridiagonalLUPivot_eq_thomasAlpha`, `Matrix.tridiagonalLUMultiplier_eq_thomasBeta`: over a
  field, the block recurrence is the Thomas recurrence.
* `Matrix.tridiagonalOf_eq_mul_of_mul_star`, `Matrix.blockTridiagonal_eq_mul_transpose`: the block
  Cholesky factorization $\operatorname{tridiag}(E, D, E^*) = GG^*$ with a block lower bidiagonal
  $G$.
* `Matrix.isStrictBlockColDiagDominant_tridiagonalOf_iff`: on a block tridiagonal matrix, dominance
  means $\|D_i^{-1}\|_1 (\|F_{i-1}\|_1 + \|E_i\|_1) < 1$ for every $i$, with invertible $D_i$.
* `Matrix.IsStrictBlockColDiagDominant.isUnit_tridiagonalLUPivot`: under dominance every pivot is
  invertible, with $\|U_i^{-1}\|_1 \le \|D_i^{-1}\|_1 / (1 - \|D_i^{-1}\|_1 \|F_{i-1}\|_1)$.
* `Matrix.IsStrictBlockColDiagDominant.lpOpNorm_tridiagonalLUMultiplier_lt_one`: under dominance
  $\|L_i\|_1 < 1$ ((4.5.7) of [golub2013matrix]).
* `Matrix.IsStrictBlockColDiagDominant.lpOpNorm_tridiagonalLUPivot_le`: under dominance
  $\|U_i\|_1 \le \|A\|_1$ ((4.5.8) of [golub2013matrix]).
* `Matrix.IsStrictBlockColDiagDominant.isUnit_blockTridiagonal`: a block tridiagonal matrix with
  strict block column diagonal dominance is nonsingular.
* `Matrix.IsBlockLU.toBlock_recurrence_of_blockTridiagonal`: the block Thomas recurrence for a block
  LU factorization in the labelling form of `Matrix.IsBlockLU` ([quarteroni2000numerical], (3.58)).

## Implementation notes

* `Matrix.blockTridiagonal E D F` is `Matrix.comp` applied to `Matrix.tridiagonalOf E D F`. The
  blocks come in the order of `Matrix.tridiagonalOf`: subdiagonal, diagonal, superdiagonal. Since
  `Matrix.compRingEquiv` is a ring isomorphism, products and inverses transfer between the block
  ring and the flattened matrices.
* The recurrence uses `Ring.inverse`, which is $0$ at a non-unit. The sequences $E$, $D$, $F$ are
  indexed by $\mathbb{N}$, as for the scalar Thomas recurrence `Matrix.thomasAlpha` of
  `Numlib.LinearAlgebra.Matrix.LU`.
* The norm $\|\cdot\|_1$ is `Matrix.lpOpNorm 1`, the matrix norm induced by the vector $1$-norm. The
  Neumann bound behind the dominance results is `Matrix.inducedNorm_inv_one_sub_le` of
  `Numlib.Analysis.Matrix.OperatorNorm`.
* `Matrix.IsBlockLU.blockBidiagonal_of_blockTridiagonal` of `Numlib.LinearAlgebra.Matrix.LU` states
  that the factors of a block LU factorization of a block tridiagonal matrix are block bidiagonal,
  with blocks given by a labelling of the indices. This module gives the constructive form with the
  recurrence, and `Matrix.IsBlockLU.toBlock_recurrence_of_blockTridiagonal` reads the recurrence off
  a factorization in the labelling form.
-/

open Finset

namespace Matrix

/-! ### The block tridiagonal matrix -/

section Block

variable {R : Type*} {N q : ℕ}

/-- The **block tridiagonal matrix** with subdiagonal blocks $E_0, \dots, E_{N-1}$, diagonal blocks
$D_0, \dots, D_N$ and superdiagonal blocks $F_0, \dots, F_{N-1}$, all of size $q \times q$
([golub2013matrix], (4.5.2)), as a matrix of order $(N + 1)q$:
$$\operatorname{tridiag}(E, D, F) = \begin{bmatrix} D_0 & F_0 & & \\ E_0 & D_1 & \ddots & \\ &
  \ddots & \ddots & F_{N-1} \\ & & E_{N-1} & D_N \end{bmatrix}.$$

It is the tridiagonal matrix `Matrix.tridiagonalOf E D F` over the ring of $q \times q$
matrices, flattened by `Matrix.comp`. The indices of the flattened matrix are pairs (block
index, index within the block). -/
def blockTridiagonal [Zero R] (E : Fin N → Matrix (Fin q) (Fin q) R)
    (D : Fin (N + 1) → Matrix (Fin q) (Fin q) R) (F : Fin N → Matrix (Fin q) (Fin q) R) :
    Matrix (Fin (N + 1) × Fin q) (Fin (N + 1) × Fin q) R :=
  comp _ _ _ _ R (tridiagonalOf E D F)

/-- The entry $(k, l)$ of the block $(i, j)$ of $\operatorname{tridiag}(E, D, F)$ is the entry
$(k, l)$ of the block $(i, j)$ of the tridiagonal matrix over the block ring. -/
theorem blockTridiagonal_apply [Zero R] (E : Fin N → Matrix (Fin q) (Fin q) R)
    (D : Fin (N + 1) → Matrix (Fin q) (Fin q) R) (F : Fin N → Matrix (Fin q) (Fin q) R)
    (i j : Fin (N + 1)) (k l : Fin q) :
    blockTridiagonal E D F (i, k) (j, l) = tridiagonalOf E D F i j k l := rfl

/-- For blocks given by sequences $E$, $D$, $F$ indexed by $\mathbb{N}$, the entry $(k, l)$ of the
block $(i, j)$ of $\operatorname{tridiag}(E, D, F)$ is $(D_i)_{kl}$ if $i = j$, $(E_j)_{kl}$ if
$i = j + 1$, $(F_i)_{kl}$ if $j = i + 1$, and $0$ otherwise. -/
theorem blockTridiagonal_apply_eq_ite [Zero R] (E D F : ℕ → Matrix (Fin q) (Fin q) R)
    (i j : Fin (N + 1)) (k l : Fin q) :
    blockTridiagonal (fun a : Fin N => E a) (fun a : Fin (N + 1) => D a) (fun a : Fin N => F a)
        (i, k) (j, l) =
      if (i : ℕ) = j then D i k l else if (i : ℕ) = j + 1 then E j k l
        else if (j : ℕ) = i + 1 then F i k l else 0 := by
  rw [blockTridiagonal_apply]
  simp only [tridiagonalOf, of_apply]
  split_ifs <;> rfl

end Block

/-!
### The block LU recurrence

The block LU factorization of [golub2013matrix], (4.5.3)–(4.5.4), is a recurrence in a
noncommutative ring $R$. The pivots are $U_0 = D_0$ and $U_{i+1} = D_{i+1} - E_i U_i^{-1} F_i$, and
the multipliers are $L_i = E_i U_i^{-1}$. If $U_0, \dots, U_{N-1}$ are units, then
$\operatorname{tridiag}(E, D, F)$ is the product of the unit lower bidiagonal matrix
$\operatorname{tridiag}(L, 1, 0)$ and the upper bidiagonal matrix $\operatorname{tridiag}(0, U, F)$.
Over a field, this is the scalar Thomas recurrence of `Numlib.LinearAlgebra.Matrix.LU`.
-/

section Recurrence

variable {R : Type*} [Ring R]

/-- The **pivots** of the block LU recurrence ([golub2013matrix], (4.5.4)) over a ring $R$, for
sequences $E$, $D$, $F$ in $R$:
$$U_0 = D_0, \qquad U_{i+1} = D_{i+1} - E_i U_i^{-1} F_i.$$

The inverse is `Ring.inverse`, which is $0$ at a non-unit. -/
noncomputable def tridiagonalLUPivot (E D F : ℕ → R) : ℕ → R
  | 0 => D 0
  | i + 1 => D (i + 1) - E i * Ring.inverse (tridiagonalLUPivot E D F i) * F i

/-- The **multipliers** of the block LU recurrence ([golub2013matrix], (4.5.4)):
$L_i = E_i U_i^{-1}$, the solution of $L_i U_i = E_i$ when $U_i$ is a unit.

The inverse is `Ring.inverse`, which is $0$ at a non-unit. -/
noncomputable def tridiagonalLUMultiplier (E D F : ℕ → R) (i : ℕ) : R :=
  E i * Ring.inverse (tridiagonalLUPivot E D F i)

variable (E D F : ℕ → R)

/-- The first pivot is the first diagonal block: $U_0 = D_0$. -/
@[simp]
theorem tridiagonalLUPivot_zero : tridiagonalLUPivot E D F 0 = D 0 := rfl

/-- The pivot recurrence in terms of the multipliers: $U_{i+1} = D_{i+1} - L_i F_i$. -/
theorem tridiagonalLUPivot_succ (i : ℕ) :
    tridiagonalLUPivot E D F (i + 1) = D (i + 1) - tridiagonalLUMultiplier E D F i * F i := rfl

/-- If the pivot $U_i$ is a unit, then the multiplier satisfies $L_i U_i = E_i$. -/
theorem tridiagonalLUMultiplier_mul_tridiagonalLUPivot {i : ℕ}
    (h : IsUnit (tridiagonalLUPivot E D F i)) :
    tridiagonalLUMultiplier E D F i * tridiagonalLUPivot E D F i = E i :=
  Ring.inverse_mul_cancel_right _ _ h

/-- **The block LU factorization** ([golub2013matrix], (4.5.3)). Let $R$ be a ring, and let $E$,
$D$, $F$ be sequences in $R$. If the pivots $U_0, \dots, U_{N-1}$ are units, then
$$\operatorname{tridiag}(E, D, F) = \operatorname{tridiag}(L, 1, 0) \cdot
  \operatorname{tridiag}(0, U, F),$$
the product of a unit lower bidiagonal and an upper bidiagonal matrix of order $N + 1$ over $R$.

There is no hypothesis on the last pivot $U_N$, which may be singular, as for the scalar LU
factorization. The tridiagonal matrices are `Matrix.tridiagonalOf` with the first $N$, $N + 1$
and $N$ terms of the sequences. -/
theorem tridiagonalOf_eq_mul_of_isUnit_tridiagonalLUPivot {N : ℕ}
    (hU : ∀ i, i < N → IsUnit (tridiagonalLUPivot E D F i)) :
    tridiagonalOf (N := N) (fun i => E i) (fun i => D i) (fun i => F i)
      = tridiagonalOf (fun i => tridiagonalLUMultiplier E D F i) 1 0
        * tridiagonalOf 0 (fun i => tridiagonalLUPivot E D F i) (fun i => F i) := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  change _ = (tridiagonalOf (fun i : Fin N => tridiagonalLUMultiplier E D F i) 1 0 *ᵥ
    fun r => tridiagonalOf 0 (fun i : Fin (N + 1) => tridiagonalLUPivot E D F i)
      (fun i : Fin N => F i) r j) i
  rw [tridiagonalOf_mulVec]
  simp only [tridiagonalOf, of_apply, Pi.one_apply, Pi.zero_apply, one_mul, zero_mul]
  split_ifs <;> first
    | (exfalso; omega)
    | (simp only [add_zero, zero_add, mul_zero]; done)
    | (have h1 : (i : ℕ) - 1 = j := by omega
       simp only [h1, tridiagonalLUMultiplier_mul_tridiagonalLUPivot E D F (hU j (by omega)),
         add_zero, zero_add]
       done)
    | (have h0 : (i : ℕ) = 0 := by omega
       simp only [h0, tridiagonalLUPivot_zero, add_zero, zero_add])
    | (obtain ⟨i', hi'⟩ : ∃ i', (i : ℕ) = i' + 1 := ⟨(i : ℕ) - 1, by omega⟩
       simp only [hi', Nat.add_sub_cancel, tridiagonalLUPivot_succ]
       abel1)

/-- Over a field, the pivots and the multipliers of the block recurrence are the Thomas pivots and
multipliers, proved together by one induction. -/
private theorem tridiagonalLUPivot_eq_thomasAlpha_aux {K : Type*} [Field K] (E D F : ℕ → K)
    (i : ℕ) :
    tridiagonalLUPivot E D F i = thomasAlpha D (fun j => E (j - 1)) F i
      ∧ tridiagonalLUMultiplier E D F i = thomasBeta D (fun j => E (j - 1)) F (i + 1) := by
  induction i with
  | zero =>
    refine ⟨rfl, ?_⟩
    rw [tridiagonalLUMultiplier, thomasBeta_succ, Ring.inverse_eq_inv', div_eq_mul_inv]
    rfl
  | succ i ih =>
    have hU : tridiagonalLUPivot E D F (i + 1)
        = thomasAlpha D (fun j => E (j - 1)) F (i + 1) := by
      rw [tridiagonalLUPivot_succ, thomasAlpha_succ, ih.2]
    refine ⟨hU, ?_⟩
    rw [tridiagonalLUMultiplier, thomasBeta_succ, Ring.inverse_eq_inv', hU, div_eq_mul_inv]
    rfl

/-- **Over a field, the block pivots are the Thomas pivots** ([quarteroni2000numerical], (3.53)).
Let $K$ be a field and let $E$, $D$, $F$ be sequences in $K$. Then $U_i = \alpha_i$ for every
$i$, where $\alpha$ is the Thomas recurrence `Matrix.thomasAlpha` with diagonal $a = D$,
superdiagonal $c = F$ and subdiagonal read one row lower, $b_j = E_{j-1}$. -/
theorem tridiagonalLUPivot_eq_thomasAlpha {K : Type*} [Field K] (E D F : ℕ → K) (i : ℕ) :
    tridiagonalLUPivot E D F i = thomasAlpha D (fun j => E (j - 1)) F i :=
  (tridiagonalLUPivot_eq_thomasAlpha_aux E D F i).1

/-- **Over a field, the block multipliers are the shifted Thomas multipliers**
([quarteroni2000numerical], (3.53)). Let $K$ be a field and let $E$, $D$, $F$ be sequences in
$K$. Then $L_i = \beta_{i+1}$ for every $i$, where $\beta$ is `Matrix.thomasBeta` with diagonal
$a = D$, superdiagonal $c = F$ and subdiagonal $b_j = E_{j-1}$. -/
theorem tridiagonalLUMultiplier_eq_thomasBeta {K : Type*} [Field K] (E D F : ℕ → K) (i : ℕ) :
    tridiagonalLUMultiplier E D F i = thomasBeta D (fun j => E (j - 1)) F (i + 1) :=
  (tridiagonalLUPivot_eq_thomasAlpha_aux E D F i).2

end Recurrence

/-! ### The block Cholesky factorization -/

section Cholesky

variable {R : Type*} [Ring R] [StarRing R]

/-- **The block Cholesky factorization of a block tridiagonal matrix** ([golub2013matrix], §4.5 and
§11.5.9), with the factors given. Let $R$ be a ring with an involution $*$, and let $E$, $D$,
$G$, $F$ be sequences in $R$ with
$$F_i G_i^* = E_i \ (i < N), \qquad G_0 G_0^* = D_0, \qquad G_{i+1} G_{i+1}^* + F_i F_i^* =
  D_{i+1} \ (i < N).$$
Then
$$\operatorname{tridiag}(E, D, E^*) = \operatorname{tridiag}(F, G, 0) \cdot
  \operatorname{tridiag}(0, G^*, F^*),$$
a lower bidiagonal matrix times its conjugate transpose.

The involution acts block by block. In the block ring of real $q \times q$ matrices, $*$ is the
transpose. The sequences are indexed by $\mathbb{N}$, as in
`Matrix.tridiagonalOf_eq_mul_of_isUnit_tridiagonalLUPivot`. -/
theorem tridiagonalOf_eq_mul_of_mul_star {N : ℕ} (E D G F : ℕ → R)
    (hFG : ∀ i, i < N → F i * star (G i) = E i) (h0 : G 0 * star (G 0) = D 0)
    (hS : ∀ i, i < N → G (i + 1) * star (G (i + 1)) + F i * star (F i) = D (i + 1)) :
    tridiagonalOf (N := N) (fun i => E i) (fun i => D i) (fun i => star (E i))
      = tridiagonalOf (fun i => F i) (fun i => G i) 0
        * tridiagonalOf 0 (fun i => star (G i)) (fun i => star (F i)) := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  change _ = (tridiagonalOf (fun i : Fin N => F i) (fun i : Fin (N + 1) => G i) 0 *ᵥ
    fun r => tridiagonalOf 0 (fun i : Fin (N + 1) => star (G i))
      (fun i : Fin N => star (F i)) r j) i
  rw [tridiagonalOf_mulVec]
  simp only [tridiagonalOf, of_apply, Pi.zero_apply, zero_mul]
  split_ifs <;> simp only [mul_zero, zero_add, add_zero] <;> first
    | (exfalso; omega)
    | (have h0' : (i : ℕ) = 0 := by omega
       rw [h0', h0])
    | (obtain ⟨i', hi'⟩ : ∃ i', (i : ℕ) = i' + 1 := ⟨(i : ℕ) - 1, by omega⟩
       rw [hi', Nat.add_sub_cancel, ← hS i' (by omega), add_comm])
    | (have h1 : (i : ℕ) - 1 = j := by omega
       rw [h1, hFG j (by omega)])
    | rw [← hFG i (by omega), star_mul, star_star]

/-- **The block Cholesky factorization, flattened** ([golub2013matrix], §11.5.9). Let $E_i$, $D_i$,
$G_i$, $F_i$ be real $q \times q$ matrices with
$$F_i G_i^T = E_i \ (i < N), \qquad G_0 G_0^T = D_0, \qquad G_{i+1} G_{i+1}^T + F_i F_i^T =
  D_{i+1} \ (i < N).$$
Then the block tridiagonal matrix $A = \operatorname{tridiag}(E, D, E^T)$ is
$A = \mathcal{G} \mathcal{G}^T$, where $\mathcal{G} = \operatorname{tridiag}(F, G, 0)$ is the
block lower bidiagonal matrix with diagonal blocks $G_0, \dots, G_N$ and subdiagonal blocks
$F_0, \dots, F_{N-1}$.

The proof transfers `Matrix.tridiagonalOf_eq_mul_of_mul_star` along the ring isomorphism
`Matrix.compRingEquiv`. -/
theorem blockTridiagonal_eq_mul_transpose {N q : ℕ} (E D G F : ℕ → Matrix (Fin q) (Fin q) ℝ)
    (hFG : ∀ i, i < N → F i * (G i)ᵀ = E i) (h0 : G 0 * (G 0)ᵀ = D 0)
    (hS : ∀ i, i < N → G (i + 1) * (G (i + 1))ᵀ + F i * (F i)ᵀ = D (i + 1)) :
    blockTridiagonal (N := N) (fun i => E i) (fun i => D i) (fun i => (E i)ᵀ) =
      blockTridiagonal (fun i => F i) (fun i => G i) 0 *
        (blockTridiagonal (N := N) (fun i => F i) (fun i => G i) 0)ᵀ := by
  have hstar : ∀ M : Matrix (Fin q) (Fin q) ℝ, star M = Mᵀ := fun M =>
    (star_eq_conjTranspose M).trans (conjTranspose_eq_transpose_of_trivial M)
  have h := tridiagonalOf_eq_mul_of_mul_star (N := N) E D G F (by simpa only [hstar] using hFG)
    (by simpa only [hstar] using h0) (by simpa only [hstar] using hS)
  simp only [hstar] at h
  have hT : (tridiagonalOf (N := N) (fun i => F i) (fun i => G i) 0)ᵀ.map transpose =
      tridiagonalOf 0 (fun i => (G i)ᵀ) (fun i => (F i)ᵀ) := by
    rw [tridiagonalOf_transpose]
    ext i j : 1
    simp only [map_apply, tridiagonalOf, of_apply]
    split_ifs <;> simp
  rw [blockTridiagonal, blockTridiagonal, transpose_comp, hT, h, ← compRingEquiv_apply,
    ← compRingEquiv_apply, ← compRingEquiv_apply, map_mul]

end Cholesky

/-!
### Block diagonal dominance

Block column diagonal dominance in the norm $\|\cdot\|_1$ induced by the vector $1$-norm is (4.5.6)
of [golub2013matrix]; it goes back to Feingold and Varga (1962). On
$\operatorname{tridiag}(E, D, F)$ it reads $\|D_i^{-1}\|_1 (\|F_{i-1}\|_1 + \|E_i\|_1) < 1$. It
makes every pivot invertible with $\|U_i^{-1}\|_1 \le \|D_i^{-1}\|_1 / (1 - \|D_i^{-1}\|_1
\|F_{i-1}\|_1)$, the multipliers contractive, $\|L_i\|_1 < 1$, the pivots bounded by the matrix,
$\|U_i\|_1 \le \|A\|_1$, and the matrix nonsingular.
-/

section Dominance

variable {𝕜 : Type*} [RCLike 𝕜] {q N : ℕ}

/-- **Strict block column diagonal dominance** in the norm $\|\cdot\|_1$. A square matrix $A$ whose
entries are $q \times q$ blocks $A_{ij}$ is strictly block column diagonally dominant if, for
every $j$, the diagonal block $A_{jj}$ is invertible and
$$\|A_{jj}^{-1}\|_1 \sum_{i \ne j} \|A_{ij}\|_1 < 1.$$
This is (4.5.6) of [golub2013matrix] for block tridiagonal matrices, and the block analogue of
column diagonal dominance due to Feingold and Varga (1962).

The source writes the condition without the invertibility of the diagonal blocks, which the norm
$\|A_{jj}^{-1}\|_1$ presupposes. The norm $\|\cdot\|_1$ is `Matrix.lpOpNorm 1`, the matrix norm
induced by the vector $1$-norm. -/
def IsStrictBlockColDiagDominant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (Matrix (Fin q) (Fin q) 𝕜)) : Prop :=
  ∀ j, IsUnit (A j j) ∧ lpOpNorm 1 (A j j)⁻¹ * ∑ i ∈ univ.erase j, lpOpNorm 1 (A i j) < 1

/-- The sum of the norms $\|\cdot\|_1$ of the off-diagonal blocks in block column $i$ of
$\operatorname{tridiag}(E, D, F)$ with $N + 1$ block rows ([golub2013matrix], (4.5.6), with
indices from $0$):
$$\|F_{i-1}\|_1 + \|E_i\|_1,$$
where the term $\|F_{i-1}\|_1$ is $0$ for $i = 0$ and the term $\|E_i\|_1$ is $0$ for $i \ge N$. -/
noncomputable def blockColOffNorm (E F : ℕ → Matrix (Fin q) (Fin q) 𝕜) (N i : ℕ) : ℝ :=
  (if i = 0 then 0 else lpOpNorm 1 (F (i - 1))) + (if i < N then lpOpNorm 1 (E i) else 0)

/-- **Block dominance of a block tridiagonal matrix** ([golub2013matrix], (4.5.6), with indices from
$0$). The matrix $\operatorname{tridiag}(E, D, F)$ with $N + 1$ block rows is strictly block
column diagonally dominant if and only if, for every $i \le N$, $D_i$ is invertible and
$$\|D_i^{-1}\|_1 (\|F_{i-1}\|_1 + \|E_i\|_1) < 1,$$
where $\|F_{-1}\|_1 = 0$ and $\|E_N\|_1 = 0$.

Block column $i$ has the off-diagonal blocks $F_{i-1}$ and $E_i$ only. The sum of their norms is
`Matrix.blockColOffNorm E F N i`. -/
theorem isStrictBlockColDiagDominant_tridiagonalOf_iff (E D F : ℕ → Matrix (Fin q) (Fin q) 𝕜) :
    (tridiagonalOf (N := N) (fun i => E i) (fun i => D i)
        (fun i => F i)).IsStrictBlockColDiagDominant ↔
      ∀ i ≤ N, IsUnit (D i) ∧ lpOpNorm 1 (D i)⁻¹ * blockColOffNorm E F N i < 1 := by
  set T := tridiagonalOf (N := N) (fun i => E i) (fun i => D i) (fun i => F i) with hT
  have hcol : ∀ j : Fin (N + 1), ∑ r ∈ univ.erase j, lpOpNorm 1 (T r j)
      = blockColOffNorm E F N j := by
    intro j
    rw [blockColOffNorm]
    have hg : ∑ r ∈ univ.erase j, lpOpNorm 1 (T r j)
        = ∑ r, (if r = j then 0 else lpOpNorm 1 (T r j)) := by
      rw [← Finset.sum_erase univ (f := fun r => if r = j then 0 else lpOpNorm 1 (T r j))
        (a := j) (by simp)]
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [ite_eq_right (Finset.ne_of_mem_erase hr)]
    have hterm : ∀ r : Fin (N + 1), (if r = j then 0 else lpOpNorm 1 (T r j))
        = (if h : (r : ℕ) = j + 1 then lpOpNorm 1 (E j) else 0)
          + (if h : (r : ℕ) + 1 = j then lpOpNorm 1 (F r) else 0) := by
      intro r
      simp only [hT, tridiagonalOf, of_apply, Fin.ext_iff]
      split_ifs <;> first | (exfalso; omega) | simp
    rw [hg, Finset.sum_congr rfl fun r _ => hterm r, Finset.sum_add_distrib,
      sum_dite_val_eq_add_one, sum_dite_val_add_one_eq, add_comm]
    congr 1
    · by_cases h : (j : ℕ) = 0
      · rw [dite_eq_right (by omega), ite_eq_left h]
      · rw [dite_eq_left (by omega), ite_eq_right h]
    · by_cases h : (j : ℕ) < N
      · rw [dite_eq_left (by omega), ite_eq_left h]
      · rw [dite_eq_right (by omega), ite_eq_right h]
  constructor
  · intro h i hi
    have hj := h ⟨i, by omega⟩
    rw [hcol, hT, tridiagonalOf_apply_self] at hj
    exact hj
  · intro h j
    rw [hcol, hT, tridiagonalOf_apply_self]
    exact h j (by omega)

/-- Every matrix of size $0 \times 0$ has norm $\|\cdot\|_1$ equal to $0$. -/
private theorem lpOpNorm_eq_zero_of_fin_zero (A : Matrix (Fin 0) (Fin 0) 𝕜) :
    lpOpNorm 1 A = 0 := by
  rw [Subsingleton.elim A 0, lpOpNorm_zero]

/-- The column sums of a product satisfy $\sum_k |(LM)_{kc}| \le \|L\|_1 \sum_k |M_{kc}|$. -/
private theorem sum_norm_mul_apply_le {m : Type*} [Fintype m] [DecidableEq m]
    (L M : Matrix m m 𝕜) (c : m) : ∑ k, ‖(L * M) k c‖ ≤ lpOpNorm 1 L * ∑ k, ‖M k c‖ := by
  have h := lpSeminorm_mulVec_le 1 L fun k => M k c
  simp only [lpSeminorm_apply, PiLp.norm_eq_of_L1] at h
  exact h

variable {E D F : ℕ → Matrix (Fin q) (Fin q) 𝕜}

/-- The multiplier bound $\|L_i\|_1 < 1$ for $i < N$, from the bound on $\|U_i^{-1}\|_1$ and the
dominance in block column $i$. -/
private theorem lpOpNorm_multiplier_lt_one {i : ℕ} (hN : i < N)
    (hd : IsUnit (D i) ∧ lpOpNorm 1 (D i)⁻¹ * blockColOffNorm E F N i < 1)
    (hU : lpOpNorm 1 (tridiagonalLUPivot E D F i)⁻¹
      ≤ lpOpNorm 1 (D i)⁻¹ /
        (1 - lpOpNorm 1 (D i)⁻¹ * (if i = 0 then 0 else lpOpNorm 1 (F (i - 1)))))
    : lpOpNorm 1 (tridiagonalLUMultiplier E D F i) < 1 := by
  set a := lpOpNorm 1 (D i)⁻¹
  set f := if i = 0 then 0 else lpOpNorm 1 (F (i - 1))
  have ha : 0 ≤ a := lpOpNorm_nonneg _ _
  have hf : 0 ≤ f := by simp only [f]; split_ifs <;> first | rfl | exact lpOpNorm_nonneg _ _
  have he : 0 ≤ lpOpNorm 1 (E i) := lpOpNorm_nonneg _ _
  rw [blockColOffNorm, ite_eq_left hN] at hd
  have hden : 0 < 1 - a * f := by nlinarith [hd.2]
  calc lpOpNorm 1 (tridiagonalLUMultiplier E D F i)
      ≤ lpOpNorm 1 (E i) * lpOpNorm 1 (tridiagonalLUPivot E D F i)⁻¹ := by
        rw [tridiagonalLUMultiplier, ← nonsing_inv_eq_ringInverse]
        exact lpOpNorm_mul_le _ _ _
    _ ≤ lpOpNorm 1 (E i) * (a / (1 - a * f)) := mul_le_mul_of_nonneg_left hU he
    _ < 1 := by
        rw [← mul_div_assoc, div_lt_one hden]
        nlinarith [hd.2]

/-- Under dominance, the pivots $U_i$, $i \le N$, are invertible with the bound on $\|U_i^{-1}\|_1$
of `Matrix.IsStrictBlockColDiagDominant.isUnit_tridiagonalLUPivot`, for blocks of positive size. -/
private theorem pivot_of_dominant (hq : 0 < q)
    (hd : ∀ i ≤ N, IsUnit (D i) ∧ lpOpNorm 1 (D i)⁻¹ * blockColOffNorm E F N i < 1) :
    ∀ i ≤ N, IsUnit (tridiagonalLUPivot E D F i) ∧ lpOpNorm 1 (tridiagonalLUPivot E D F i)⁻¹
      ≤ lpOpNorm 1 (D i)⁻¹ / (1 - lpOpNorm 1 (D i)⁻¹ *
        (if i = 0 then 0 else lpOpNorm 1 (F (i - 1)))) := by
  have : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨(hd 0 (Nat.zero_le _)).1, ?_⟩
    simp
  | succ i ih =>
    intro hi
    obtain ⟨hUi, hUi'⟩ := ih (by omega)
    have hL := lpOpNorm_multiplier_lt_one (by omega) (hd i (by omega)) hUi'
    obtain ⟨hD, hdom⟩ := hd (i + 1) hi
    simp only [blockColOffNorm, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel] at hdom ⊢
    set a := lpOpNorm 1 (D (i + 1))⁻¹
    have ha : 0 ≤ a := lpOpNorm_nonneg _ _
    have hF : 0 ≤ lpOpNorm 1 (F i) := lpOpNorm_nonneg _ _
    have he : 0 ≤ (if i + 1 < N then lpOpNorm 1 (E (i + 1)) else 0) := by
      split_ifs <;> first | rfl | exact lpOpNorm_nonneg _ _
    set X := (D (i + 1))⁻¹ * (tridiagonalLUMultiplier E D F i * F i)
    have hX : lpOpNorm 1 X ≤ a * lpOpNorm 1 (F i) := by
      calc lpOpNorm 1 X
          ≤ a * lpOpNorm 1 (tridiagonalLUMultiplier E D F i * F i) := lpOpNorm_mul_le _ _ _
        _ ≤ a * (lpOpNorm 1 (tridiagonalLUMultiplier E D F i) * lpOpNorm 1 (F i)) :=
            mul_le_mul_of_nonneg_left (lpOpNorm_mul_le _ _ _) ha
        _ ≤ a * lpOpNorm 1 (F i) := by
            refine mul_le_mul_of_nonneg_left ?_ ha
            nlinarith [lpOpNorm_nonneg 1 (tridiagonalLUMultiplier E D F i)]
    have hX1 : lpOpNorm 1 X < 1 := by nlinarith
    have hdet : IsUnit (D (i + 1)).det := (isUnit_iff_isUnit_det _).mp hD
    have hUeq : tridiagonalLUPivot E D F (i + 1) = D (i + 1) * (1 - X) := by
      rw [tridiagonalLUPivot_succ, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc,
        mul_nonsing_inv _ hdet, Matrix.one_mul]
    have hXi : inducedNorm (lpSeminorm 1) (lpSeminorm 1) X < 1 := by
      rwa [← lpOpNorm_eq_inducedNorm]
    have h1X : IsUnit (1 - X) := isUnit_one_sub_of_inducedNorm_lt_one (lpSeminorm_definite 1) hXi
    have hinv : lpOpNorm 1 (1 - X)⁻¹ ≤ 1 / (1 - lpOpNorm 1 X) := by
      have := inducedNorm_inv_one_sub_le (lpSeminorm_definite 1) hXi
      rwa [← lpOpNorm_eq_inducedNorm, ← lpOpNorm_eq_inducedNorm] at this
    refine ⟨hUeq ▸ hD.mul h1X, ?_⟩
    rw [hUeq, Matrix.mul_inv_rev]
    have hden : 0 < 1 - a * lpOpNorm 1 (F i) := by nlinarith
    calc lpOpNorm 1 ((1 - X)⁻¹ * (D (i + 1))⁻¹)
        ≤ lpOpNorm 1 (1 - X)⁻¹ * a := lpOpNorm_mul_le _ _ _
      _ ≤ 1 / (1 - lpOpNorm 1 X) * a := mul_le_mul_of_nonneg_right hinv ha
      _ ≤ 1 / (1 - a * lpOpNorm 1 (F i)) * a := by
          refine mul_le_mul_of_nonneg_right ?_ ha
          exact one_div_le_one_div_of_le hden (by linarith)
      _ = a / (1 - a * lpOpNorm 1 (F i)) := by ring

/-- **Block dominance makes the pivots invertible** ([golub2013matrix], §4.5.2). Let
$\operatorname{tridiag}(E, D, F)$ with $N + 1$ block rows be strictly block column diagonally
dominant. Then for every $i \le N$ the pivot $U_i$ is invertible and
$$\|U_i^{-1}\|_1 \le \frac{\|D_i^{-1}\|_1}{1 - \|D_i^{-1}\|_1 \|F_{i-1}\|_1},$$
where $\|F_{-1}\|_1 = 0$. Thus the factorization (4.5.3) exists.

The induction carries $\|L_{i-1}\|_1 < 1$. Then $U_i = D_i (I - D_i^{-1} L_{i-1} F_{i-1})$ with
$\|D_i^{-1} L_{i-1} F_{i-1}\|_1 \le \|D_i^{-1}\|_1 \|F_{i-1}\|_1 < 1$, and the Neumann series
gives the bound. -/
theorem IsStrictBlockColDiagDominant.isUnit_tridiagonalLUPivot
    (h : (tridiagonalOf (N := N) (fun i => E i) (fun i => D i)
      (fun i => F i)).IsStrictBlockColDiagDominant) {i : ℕ} (hi : i ≤ N) :
    IsUnit (tridiagonalLUPivot E D F i) ∧ lpOpNorm 1 (tridiagonalLUPivot E D F i)⁻¹
      ≤ lpOpNorm 1 (D i)⁻¹ / (1 - lpOpNorm 1 (D i)⁻¹ *
        (if i = 0 then 0 else lpOpNorm 1 (F (i - 1)))) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · exact ⟨isUnit_of_subsingleton _, by simp [lpOpNorm_eq_zero_of_fin_zero]⟩
  exact pivot_of_dominant hq ((isStrictBlockColDiagDominant_tridiagonalOf_iff E D F).mp h) i hi

/-- **Equation (4.5.7)** of [golub2013matrix], strict form. Let $\operatorname{tridiag}(E, D, F)$
with $N + 1$ block rows be strictly block column diagonally dominant. Then for every $i < N$ the
multiplier satisfies $\|L_i\|_1 < 1$.

The reason is $\|E_i U_i^{-1}\|_1 \le \|E_i\|_1 \|D_i^{-1}\|_1 / (1 - \|D_i^{-1}\|_1
\|F_{i-1}\|_1) < 1$. -/
theorem IsStrictBlockColDiagDominant.lpOpNorm_tridiagonalLUMultiplier_lt_one
    (h : (tridiagonalOf (N := N) (fun i => E i) (fun i => D i)
      (fun i => F i)).IsStrictBlockColDiagDominant) {i : ℕ} (hi : i < N) :
    lpOpNorm 1 (tridiagonalLUMultiplier E D F i) < 1 :=
  lpOpNorm_multiplier_lt_one hi ((isStrictBlockColDiagDominant_tridiagonalOf_iff E D F).mp h i
    hi.le) (h.isUnit_tridiagonalLUPivot hi.le).2

/-- **Equation (4.5.7)** of [golub2013matrix], as printed. Let $\operatorname{tridiag}(E, D, F)$
with $N + 1$ block rows be strictly block column diagonally dominant. Then for every $i < N$ the
multiplier satisfies $\|L_i\|_1 \le 1$.

The strict inequality is
`Matrix.IsStrictBlockColDiagDominant.lpOpNorm_tridiagonalLUMultiplier_lt_one`. -/
theorem IsStrictBlockColDiagDominant.lpOpNorm_tridiagonalLUMultiplier_le
    (h : (tridiagonalOf (N := N) (fun i => E i) (fun i => D i)
      (fun i => F i)).IsStrictBlockColDiagDominant) {i : ℕ} (hi : i < N) :
    lpOpNorm 1 (tridiagonalLUMultiplier E D F i) ≤ 1 :=
  (h.lpOpNorm_tridiagonalLUMultiplier_lt_one hi).le

/-- **Equation (4.5.8)** of [golub2013matrix]. Let $\operatorname{tridiag}(E, D, F)$ with $N + 1$
block rows be strictly block column diagonally dominant, and let $A$ be its flattening, of order
$(N + 1)q$. Then for every $i \le N$ the pivot satisfies $\|U_i\|_1 \le \|A\|_1$.

The source prints the bound $\|A_n\|_1$, which refers to no defined matrix; the statement here
reads it as $\|A\|_1$. Column by column, $U_i e_c = D_i e_c - L_{i-1} F_{i-1} e_c$ with
$\|L_{i-1}\|_1 \le 1$, and this is at most the $1$-norm of the column $(i, c)$ of $A$. -/
theorem IsStrictBlockColDiagDominant.lpOpNorm_tridiagonalLUPivot_le
    (h : (tridiagonalOf (N := N) (fun i => E i) (fun i => D i)
      (fun i => F i)).IsStrictBlockColDiagDominant) {i : ℕ} (hi : i ≤ N) :
    lpOpNorm 1 (tridiagonalLUPivot E D F i)
      ≤ lpOpNorm 1 (blockTridiagonal (fun i : Fin N => E i) (fun i : Fin (N + 1) => D i)
        fun i : Fin N => F i) := by
  set A := blockTridiagonal (fun i : Fin N => E i) (fun i : Fin (N + 1) => D i)
    fun i : Fin N => F i with hA
  -- the column sums of `A` below its norm, restricted to one or two block rows
  have hcolA : ∀ c : Fin q, ∑ p : Fin (N + 1) × Fin q, ‖A p (⟨i, by omega⟩, c)‖ ≤ lpOpNorm 1 A :=
    fun c => sum_norm_le_lpOpNorm_one A _
  have hdiag : ∀ k c, A (⟨i, by omega⟩, k) (⟨i, by omega⟩, c) = D i k c := by
    intro k c
    simp [hA, blockTridiagonal_apply]
  refine lpOpNorm_one_le_of_forall_sum_le (lpOpNorm_nonneg _ _) fun c => ?_
  refine le_trans ?_ (hcolA c)
  rw [Fintype.sum_prod_type]
  set g : Fin (N + 1) → ℝ := fun r => ∑ k, ‖A (r, k) (⟨i, by omega⟩, c)‖ with hg
  have hg0 : ∀ r, 0 ≤ g r := fun r => Finset.sum_nonneg fun k _ => norm_nonneg _
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · calc ∑ k, ‖tridiagonalLUPivot E D F 0 k c‖ = g ⟨0, by omega⟩ := by
          simp only [hg, hdiag, tridiagonalLUPivot_zero]
      _ ≤ ∑ r, g r := Finset.single_le_sum (fun r _ => hg0 r) (mem_univ _)
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have hL := h.lpOpNorm_tridiagonalLUMultiplier_le (i := i') (by omega)
    have hoff : ∀ k, A (⟨i', by omega⟩, k) (⟨i' + 1, by omega⟩, c) = F i' k c := by
      intro k
      simp only [hA, blockTridiagonal_apply, tridiagonalOf, of_apply]
      split_ifs <;> first | (exfalso; omega) | rfl
    have hne : (⟨i' + 1, by omega⟩ : Fin (N + 1)) ≠ ⟨i', by omega⟩ := by simp
    calc ∑ k, ‖tridiagonalLUPivot E D F (i' + 1) k c‖
        ≤ ∑ k, (‖D (i' + 1) k c‖ + ‖(tridiagonalLUMultiplier E D F i' * F i') k c‖) := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [tridiagonalLUPivot_succ, Matrix.sub_apply]
          exact norm_sub_le _ _
      _ ≤ ∑ k, ‖D (i' + 1) k c‖ + ∑ k, ‖F i' k c‖ := by
          rw [Finset.sum_add_distrib]
          have := sum_norm_mul_apply_le (tridiagonalLUMultiplier E D F i') (F i') c
          have hs : 0 ≤ ∑ k, ‖F i' k c‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
          nlinarith
      _ = g ⟨i' + 1, by omega⟩ + g ⟨i', by omega⟩ := by
          simp only [hg, hdiag, hoff]
      _ = ∑ r ∈ {⟨i' + 1, by omega⟩, ⟨i', by omega⟩}, g r := (Finset.sum_pair hne).symm
      _ ≤ ∑ r, g r :=
          Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun r _ _ => hg0 r

/-- **A block tridiagonal matrix with strict block column diagonal dominance is nonsingular**
([golub2013matrix], Problem P4.5.1(a), the fact that §4.5.2 presupposes). If
$\operatorname{tridiag}(E, D, F)$ with $N + 1$ block rows is strictly block column diagonally
dominant, then its flattening is a unit.

All pivots $U_0, \dots, U_N$ are invertible. So the factorization (4.5.3) is a product of a unit
lower bidiagonal matrix and an upper bidiagonal matrix with invertible diagonal blocks, both
units of the block matrix ring, and the flattening `Matrix.compRingEquiv` preserves units. -/
theorem IsStrictBlockColDiagDominant.isUnit_blockTridiagonal
    (h : (tridiagonalOf (N := N) (fun i => E i) (fun i => D i)
      (fun i => F i)).IsStrictBlockColDiagDominant) :
    IsUnit (blockTridiagonal (fun i : Fin N => E i) (fun i : Fin (N + 1) => D i)
      fun i : Fin N => F i) := by
  have hU : ∀ i, i ≤ N → IsUnit (tridiagonalLUPivot E D F i) :=
    fun i hi => (h.isUnit_tridiagonalLUPivot hi).1
  have hfac := tridiagonalOf_eq_mul_of_isUnit_tridiagonalLUPivot E D F fun i hi => hU i hi.le
  have hT : IsUnit (tridiagonalOf (N := N) (fun i => E i) (fun i => D i) (fun i => F i)) := by
    rw [hfac]
    exact (isUnit_tridiagonalOf_one_zero _).mul
      (isUnit_tridiagonalOf_zero _ _ fun i => hU i (by omega))
  exact hT.map (compRingEquiv (Fin (N + 1)) (Fin q) 𝕜)

end Dominance

/-! ### The block Thomas recurrence in the labelling form -/

section BlockLU

variable {N m : ℕ} {b : Fin N → Fin m} {K : Type*} [Field K] {A L U : Matrix (Fin N) (Fin N) K}

/-- The entry $(i, j)$ of a product of two blocks, through the block of the label $k$, is the sum of
$X_{i j'} Y_{j' j}$ over the indices $j'$ with label $k$. -/
private theorem toBlock_mul_toBlock_apply (k : Fin m) {p r : Fin N → Prop}
    (X Y : Matrix (Fin N) (Fin N) K) (i : {x : Fin N // p x}) (j : {x : Fin N // r x}) :
    (X.toBlock p (fun x => b x = k) * Y.toBlock (fun x => b x = k) r) i j =
      ∑ j' ∈ univ.filter fun x => b x = k, X i.1 j' * Y j' j.1 := by
  rw [Matrix.mul_apply]
  exact (Finset.sum_subtype _ (fun x => by simp) fun j' => X i.1 j' * Y j' j.1).symm

/-- If $A = LU$ is a block LU factorization and $U_{j' j} = 0$ for every $j'$ whose label is below
the label of $i$, then $U_{ij} = A_{ij}$. -/
private theorem upper_apply_eq (h : IsBlockLU b A L U) {i j : Fin N}
    (hlow : ∀ j', b j' < b i → U j' j = 0) : U i j = A i j := by
  have key : (L * U) i j = ((1 : Matrix (Fin N) (Fin N) K) * U) i j := by
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rcases lt_trichotomy (b j') (b i) with hb | hb | hb
    · rw [hlow j' hb, mul_zero, mul_zero]
    · rw [h.isBlockUnitLowerTriangular.apply_eq_one_of_eq i j' hb.symm]
    · rw [h.isBlockUnitLowerTriangular.blockTriangular (OrderDual.toDual_lt_toDual.2 hb),
        one_apply_ne fun hij => hb.ne (congrArg b hij), zero_mul]
  rw [h.mul_eq, Matrix.one_mul] at key
  exact key.symm

/-- **The block Thomas recurrence** ([quarteroni2000numerical], §3.8.3 and (3.58);
[golub2013matrix], (4.5.3)–(4.5.4)), in the labelling form of `Matrix.IsBlockLU`. Let $K$ be a
field, let $A$ be a square matrix over $K$ of order $N$, and let $b$ assign to each index a
block label in $\{0, \dots, m - 1\}$. Write $A_{kl}$ for the block of $A$ with row labels $k$
and column labels $l$. Assume that $A$ is block tridiagonal, that is, $A_{ij} = 0$ whenever
$b(j) + 1 < b(i)$ or $b(i) + 1 < b(j)$, and that every leading principal block submatrix, on the
indices with label at most $k$, is invertible. Let $A = LU$ be a block LU factorization along
$b$. Then:

* if $k$ is at most every label, then $U_{kk} = A_{kk}$;
* if $l = k + 1$, then $U_{kl} = A_{kl}$;
* if $l = k + 1$, then $L_{lk} U_{kk} = A_{lk}$;
* if $l = k + 1$, then $U_{ll} = A_{ll} - L_{lk} A_{kl}$.

Thus $U_1 = A_{11}$, the superdiagonal blocks of $U$ are those of $A$, and the other blocks
follow in sequence by solving $L_{i-1} U_{i-1} = A_{i,i-1}$ for the subdiagonal block of $L$ and
computing $U_i = A_{ii} - L_{i-1} A_{i-1,i}$. This is the recurrence of
`Matrix.tridiagonalLUPivot` and `Matrix.tridiagonalLUMultiplier`, for blocks given by a
labelling of the indices. By `Matrix.IsBlockLU.blockBidiagonal_of_blockTridiagonal`, the factors
are block bidiagonal. The block $A_{kl}$ is `A.toBlock (b · = k) (b · = l)`. -/
theorem IsBlockLU.toBlock_recurrence_of_blockTridiagonal (h : IsBlockLU b A L U)
    (htriL : ∀ i j, (b j : ℕ) + 1 < b i → A i j = 0)
    (htriU : ∀ i j, (b i : ℕ) + 1 < b j → A i j = 0)
    (hlead : ∀ k : Fin m, IsUnit (A.toBlock (b · ≤ k) (b · ≤ k))) :
    (∀ k : Fin m, (∀ i, k ≤ b i) →
        U.toBlock (b · = k) (b · = k) = A.toBlock (b · = k) (b · = k)) ∧
      (∀ k l : Fin m, (k : ℕ) + 1 = l →
        U.toBlock (b · = k) (b · = l) = A.toBlock (b · = k) (b · = l)) ∧
      (∀ k l : Fin m, (k : ℕ) + 1 = l →
        L.toBlock (b · = l) (b · = k) * U.toBlock (b · = k) (b · = k) =
          A.toBlock (b · = l) (b · = k)) ∧
      (∀ k l : Fin m, (k : ℕ) + 1 = l →
        U.toBlock (b · = l) (b · = l) = A.toBlock (b · = l) (b · = l) -
          L.toBlock (b · = l) (b · = k) * A.toBlock (b · = k) (b · = l)) := by
  obtain ⟨hLbd, hUbd⟩ := IsBlockLU.blockBidiagonal_of_blockTridiagonal h htriL htriU hlead
  have hsuper : ∀ {i j : Fin N}, ((b i : ℕ) + 1 = b j ∨ ∀ x, b i ≤ b x) → U i j = A i j := by
    rintro i j (hij | hmin)
    · exact upper_apply_eq h fun j' hj' => hUbd j' j (by omega)
    · exact upper_apply_eq h fun j' hj' => absurd (hmin j') (not_le.2 hj')
  refine ⟨fun k hk => ?_, fun k l hkl => ?_, fun k l hkl => ?_, fun k l hkl => ?_⟩
  · ext i j
    exact hsuper (Or.inr fun x => by rw [i.2]; exact hk x)
  · ext i j
    exact hsuper (Or.inl (by rw [i.2, j.2]; exact hkl))
  · ext i j
    rw [toBlock_mul_toBlock_apply, toBlock_apply, ← h.mul_eq, Matrix.mul_apply]
    refine Finset.sum_subset (filter_subset _ _) fun x _ hx => ?_
    have hxk : b x ≠ k := by simpa using hx
    rcases lt_or_gt_of_ne hxk with hlt | hgt
    · rw [hLbd i.1 x (by rw [i.2]; omega), zero_mul]
    · rcases eq_or_lt_of_le (show l ≤ b x from Fin.le_def.2 (by omega)) with heq | hlt'
      · rw [h.blockTriangular (show b j.1 < b x by
          rw [j.2, ← heq]; exact Fin.lt_def.2 (by omega)), mul_zero]
      · rw [h.isBlockUnitLowerTriangular.blockTriangular
          (OrderDual.toDual_lt_toDual.2 (show b i.1 < b x by rw [i.2]; exact hlt')), zero_mul]
  · ext i j
    have hone : ∀ x ∈ univ.filter fun x => b x = k,
        (1 : Matrix (Fin N) (Fin N) K) i.1 x * U x j.1 = 0 := by
      intro x hx
      have hxk : b x = k := by simpa using hx
      rw [one_apply_ne fun hij => by rw [← hij, i.2] at hxk; omega, zero_mul]
    have hrest : ∀ x ∈ univ.filter fun x => ¬ b x = k,
        L i.1 x * U x j.1 = (1 : Matrix (Fin N) (Fin N) K) i.1 x * U x j.1 := by
      intro x hx
      have hxk : b x ≠ k := by simpa using hx
      rcases lt_or_gt_of_ne hxk with hlt | hgt
      · have hne : i.1 ≠ x := fun hij => by
          rw [← hij, i.2] at hlt; exact absurd (Fin.lt_def.1 hlt) (by omega)
        rw [hLbd i.1 x (by rw [i.2]; omega), one_apply_ne hne,
          zero_mul]
      · rcases eq_or_lt_of_le (show l ≤ b x from Fin.le_def.2 (by omega)) with heq | hlt'
        · rw [h.isBlockUnitLowerTriangular.apply_eq_one_of_eq i.1 x (by rw [i.2, ← heq])]
        · have hne : i.1 ≠ x := fun hij => by
            rw [← hij, i.2] at hlt'; exact absurd hlt' (lt_irrefl _)
          rw [h.isBlockUnitLowerTriangular.blockTriangular
            (OrderDual.toDual_lt_toDual.2 (show b i.1 < b x by rw [i.2]; exact hlt')),
            one_apply_ne hne, zero_mul]
    have hsum : A i.1 j.1 =
        (∑ x ∈ univ.filter fun x => b x = k, L i.1 x * U x j.1) + U i.1 j.1 := by
      have hall : (∑ x ∈ univ.filter fun x => b x = k,
            (1 : Matrix (Fin N) (Fin N) K) i.1 x * U x j.1) +
          ∑ x ∈ univ.filter fun x => ¬ b x = k,
            (1 : Matrix (Fin N) (Fin N) K) i.1 x * U x j.1 = U i.1 j.1 := by
        rw [Finset.sum_filter_add_sum_filter_not univ (fun x => b x = k)
          fun x => (1 : Matrix (Fin N) (Fin N) K) i.1 x * U x j.1, ← Matrix.mul_apply,
          Matrix.one_mul]
      rw [Finset.sum_eq_zero hone, zero_add] at hall
      rw [← h.mul_eq, Matrix.mul_apply,
        ← Finset.sum_filter_add_sum_filter_not univ (fun x => b x = k)
          fun x => L i.1 x * U x j.1, Finset.sum_congr rfl hrest, hall]
    have hAU : ∀ x ∈ univ.filter fun x => b x = k, L i.1 x * A x j.1 = L i.1 x * U x j.1 := by
      intro x hx
      have hxk : b x = k := by simpa using hx
      rw [hsuper (Or.inl (by rw [hxk, j.2]; exact hkl))]
    rw [toBlock_apply, Matrix.sub_apply, toBlock_apply, toBlock_mul_toBlock_apply,
      Finset.sum_congr rfl hAU, hsum]
    ring

end BlockLU

end Matrix
