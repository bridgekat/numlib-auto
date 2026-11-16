/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.Permutation`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Named permutation and shift matrices

This file defines the permutation and shift matrices that recur in matrix computations, following
[golub2013matrix], §1.2.11 (exchange, downshift, perfect shuffle), §4.7.1, §4.8.2 and (12.1.7). The
indices are $0, \dots, n - 1$, and $\operatorname{rev}(i) = n - 1 - i$. The **exchange matrix**
$\mathcal{E}_n$ has ones on the antidiagonal and turns a vector upside down:
$(\mathcal{E}_n x)_i = x_{n-1-i}$. The **downshift** $\mathcal{D}_n$ pushes the components of a
vector down one place with wraparound: $(\mathcal{D}_n x)_i = x_{i-1}$, with indices modulo $n$; it
is the circulant matrix of the unit vector $e_1$, and $\mathcal{D}_n^n = I$. The mod-$p$ **perfect
shuffle** $\Pi_{p,r}$ cuts a deck of $pr$ cards into $p$ piles of $r$ cards and reassembles it by
taking one card from each pile in turn: $(\Pi_{p,r} x)_{ap + b} = x_{br + a}$ for $0 \le a < r$ and
$0 \le b < p$. It is orthogonal, and $\Pi_{p,r}^T = \Pi_{r,p}$. The **$\varphi$-cyclic shift**
$Z_\varphi$ is the downshift with the wraparound entry replaced by $\varphi$, so that
$Z_1 = \mathcal{D}_n$, $Z_0$ is the lower shift, and $Z_\varphi^n = \varphi I$.

The results that use these matrices are with their subjects: persymmetry and Toeplitz structure, the
commutation of the Kronecker product, and displacement structure.

## Main definitions

* `Matrix.exchange`: the exchange matrix $\mathcal{E}_n$, the permutation matrix of the reversal
  `Fin.revPerm`.
* `Matrix.downshift`: the downshift $\mathcal{D}_n$, the permutation matrix of the inverse of the
  rotation `finRotate n`.
* `Matrix.finPerfectShuffle`: the index map $br + a \mapsto ap + b$ of the perfect shuffle.
* `Matrix.perfectShuffle`: the perfect shuffle $\Pi_{p,r}$, the matrix of the index map
  `Matrix.finPerfectShuffle`.
* `Matrix.cyclicShift`: the $\varphi$-cyclic shift $Z_\varphi$.

## Main results

* `Matrix.exchange_eq_permMatrix`, `Matrix.exchange_mul_exchange`, `Matrix.transpose_exchange`,
  `Matrix.exchange_mul_mul_exchange_eq_submatrix`: $\mathcal{E}_n$ is a symmetric involution, and
  $\mathcal{E}_n A \mathcal{E}_n$ reverses the rows and the columns of $A$.
* `Matrix.downshift_eq_circulant`, `Matrix.downshift_pow`, `Matrix.downshift_pow_card`: the powers
  of $\mathcal{D}_n$ are the circulants of the unit vectors, and $\mathcal{D}_n^n = I$.
* `Matrix.perfectShuffle_mulVec`, `Matrix.transpose_perfectShuffle`,
  `Matrix.perfectShuffle_mul_transpose`, `Matrix.transpose_mul_perfectShuffle`: the action of
  $\Pi_{p,r}$ on a vector, $\Pi_{p,r}^T = \Pi_{r,p}$, and the orthogonality of $\Pi_{p,r}$.
* `Matrix.cyclicShift_one`, `Matrix.cyclicShift_pow_card`: $Z_1 = \mathcal{D}_n$ and
  $Z_\varphi^n = \varphi I$.

## Implementation notes

* The matrices are defined on `Fin n` as instances of Mathlib's permutation-matrix API
  (`Equiv.Perm.permMatrix`, `PEquiv.toMatrix`).
* The perfect shuffle has the type `Matrix (Fin (r * p)) (Fin (p * r)) R`. Both index types have
  $pr$ elements. Because the two types are kept apart, $\Pi_{p,r}^T = \Pi_{r,p}$ and the conjugation
  of a Kronecker product (`Numlib.LinearAlgebra.Matrix.Kronecker`) hold with no cast. Position
  $br + a$ of the input (card $a$ of pile $b$) is position $ap + b$ of the output, which is the
  index map `finProdFinEquiv (b, a) ↦ finProdFinEquiv (a, b)`.
-/

open Equiv

namespace Matrix

variable {R : Type*}

/-! ### The exchange matrix -/

section Exchange

section Basic

variable [Zero R] [One R]

/-- The **exchange matrix** $\mathcal{E}_n \in R^{n \times n}$ has ones on the antidiagonal and
zeros elsewhere, so that $\mathcal{E}_n x$ is $x$ turned upside down. It is the permutation
matrix of the reversal `Fin.revPerm`, $i \mapsto n - 1 - i$. -/
def exchange (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  (Fin.revPerm : Perm (Fin n)).permMatrix R

/-- The exchange matrix $\mathcal{E}_n$ is the permutation matrix of the reversal `Fin.revPerm`. -/
theorem exchange_eq_permMatrix (n : ℕ) :
    (exchange n : Matrix (Fin n) (Fin n) R) = (Fin.revPerm : Perm (Fin n)).permMatrix R := rfl

/-- The entries of the exchange matrix are $(\mathcal{E}_n)_{ij} = 1$ if $j = n - 1 - i$ and $0$
otherwise. -/
theorem exchange_apply (n : ℕ) (i j : Fin n) :
    (exchange n : Matrix (Fin n) (Fin n) R) i j = if j = Fin.rev i then 1 else 0 := by
  simp [exchange, PEquiv.toMatrix_apply, eq_comm]

/-- The exchange matrix is symmetric: $\mathcal{E}_n^T = \mathcal{E}_n$. -/
@[simp]
theorem transpose_exchange (n : ℕ) : (exchange n : Matrix (Fin n) (Fin n) R)ᵀ = exchange n := by
  ext i j
  simp only [transpose_apply, exchange_apply]
  exact if_congr ⟨fun h => h ▸ (Fin.rev_rev j).symm, fun h => h ▸ (Fin.rev_rev i).symm⟩ rfl rfl

end Basic

variable [NonAssocSemiring R] {n : ℕ}

/-- The exchange matrix reverses a vector: $(\mathcal{E}_n v)_i = v_{n-1-i}$. -/
@[simp]
theorem exchange_mulVec_apply (v : Fin n → R) (i : Fin n) :
    (exchange n *ᵥ v) i = v (Fin.rev i) := by
  rw [exchange_eq_permMatrix, PEquiv.toMatrix_toPEquiv_mulVec]
  rfl

/-- The exchange matrix reverses a row vector: $(v^T \mathcal{E}_n)_j = v_{n-1-j}$. -/
@[simp]
theorem vecMul_exchange_apply (v : Fin n → R) (j : Fin n) :
    (v ᵥ* exchange n) j = v (Fin.rev j) := by
  rw [exchange_eq_permMatrix, PEquiv.vecMul_toMatrix_toPEquiv]
  rfl

/-- A product with the exchange matrix on the left reverses the order of the rows:
$(\mathcal{E}_n A)_{ij} = a_{n-1-i, j}$. -/
@[simp]
theorem exchange_mul_apply {m : Type*} (A : Matrix (Fin n) m R) (i : Fin n) (j : m) :
    (exchange n * A : Matrix (Fin n) m R) i j = A (Fin.rev i) j := by
  rw [exchange_eq_permMatrix, PEquiv.toMatrix_toPEquiv_mul]
  rfl

/-- A product with the exchange matrix on the right reverses the order of the columns:
$(A \mathcal{E}_n)_{ij} = a_{i, n-1-j}$. -/
@[simp]
theorem mul_exchange_apply {m : Type*} (A : Matrix m (Fin n) R) (i : m) (j : Fin n) :
    (A * exchange n : Matrix m (Fin n) R) i j = A i (Fin.rev j) := by
  rw [exchange_eq_permMatrix, PEquiv.mul_toMatrix_toPEquiv]
  rfl

/-- The exchange matrix is an involution: $\mathcal{E}_n \mathcal{E}_n = I$. -/
@[simp]
theorem exchange_mul_exchange : (exchange n : Matrix (Fin n) (Fin n) R) * exchange n = 1 := by
  ext i j
  rw [exchange_mul_apply, exchange_apply, Matrix.one_apply, Fin.rev_rev]
  exact if_congr eq_comm rfl rfl

/-- A product with the exchange matrix on the left reverses the rows: $\mathcal{E}_n A$ is the
matrix with entries $a_{n-1-i, j}$, that is, `A.submatrix Fin.rev id`. -/
theorem exchange_mul_eq_submatrix {m : Type*} (A : Matrix (Fin n) m R) :
    exchange n * A = A.submatrix Fin.rev id := by
  ext i j
  rw [exchange_mul_apply, submatrix_apply, id]

/-- A conjugation by the exchange matrix reverses the rows and the columns:
$\mathcal{E}_n A \mathcal{E}_n$ is the matrix with entries $a_{n-1-i, n-1-j}$, that is,
`A.submatrix Fin.rev Fin.rev`. -/
theorem exchange_mul_mul_exchange_eq_submatrix (A : Matrix (Fin n) (Fin n) R) :
    exchange n * A * exchange n = A.submatrix Fin.rev Fin.rev := by
  ext i j
  rw [mul_exchange_apply, exchange_mul_apply, submatrix_apply]

end Exchange

/-! ### The downshift -/

section Downshift

section Basic

variable [Zero R] [One R]

/-- The **downshift** $\mathcal{D}_n \in R^{n \times n}$ is the permutation matrix with
$\mathcal{D}_n e_j = e_{j+1}$, with indices modulo $n$. So $\mathcal{D}_n x$ pushes the
components of $x$ down one place with wraparound. It is the permutation matrix of
`(finRotate n).symm`. -/
def downshift (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Equiv.Perm.permMatrix R (finRotate n).symm

/-- The entries of the downshift are $(\mathcal{D}_n)_{ij} = 1$ if $i = j + 1$ modulo $n$, and $0$
otherwise. -/
theorem downshift_apply (n : ℕ) (i j : Fin n) :
    (downshift n : Matrix (Fin n) (Fin n) R) i j = if finRotate n j = i then 1 else 0 := by
  simp only [downshift, Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq]
  exact if_congr (((finRotate n).symm_apply_eq).trans eq_comm) rfl rfl

/-- For $n \ge 1$, the downshift $\mathcal{D}_n$ is the circulant matrix of the unit vector $e_1$.
-/
theorem downshift_eq_circulant (n : ℕ) [NeZero n] :
    (downshift n : Matrix (Fin n) (Fin n) R) = circulant (Pi.single 1 1) := by
  ext i j
  rw [downshift_apply, circulant_apply, finRotate_apply]
  simp only [Pi.single_apply]
  exact if_congr (by rw [sub_eq_iff_eq_add, add_comm, eq_comm]) rfl rfl

end Basic

variable [Semiring R]

/-- The downshift moves a vector down one place with wraparound: $(\mathcal{D}_n x)_i = x_{i-1}$,
with indices modulo $n$. -/
theorem downshift_mulVec {n : ℕ} (x : Fin n → R) :
    downshift n *ᵥ x = x ∘ (finRotate n).symm :=
  PEquiv.toMatrix_toPEquiv_mulVec (finRotate n).symm x

open Fin.NatCast in
/-- For $n \ge 1$ and $k \in \mathbb{N}$, the power $\mathcal{D}_n^k$ is the circulant matrix of the
unit vector $e_{k \bmod n}$. -/
theorem downshift_pow (n : ℕ) [NeZero n] (k : ℕ) :
    (downshift n : Matrix (Fin n) (Fin n) R) ^ k = circulant (Pi.single (k : Fin n) 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, downshift_eq_circulant, circulant_mul]
    congr 1
    ext i
    simp only [mulVec, dotProduct, circulant_apply, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, Nat.cast_succ, sub_eq_iff_eq_add]

open Fin.NatCast in
/-- The downshift satisfies $\mathcal{D}_n^n = I$. -/
theorem downshift_pow_card (n : ℕ) : (downshift n : Matrix (Fin n) (Fin n) R) ^ n = 1 := by
  rcases n.eq_zero_or_pos with rfl | hn
  · exact Subsingleton.elim _ _
  · have := NeZero.of_pos hn
    rw [downshift_pow, Fin.natCast_self, circulant_single_one]

end Downshift

/-! ### The perfect shuffle -/

section PerfectShuffle

/-- The **perfect-shuffle index map** $\{0, \dots, pr - 1\} \to \{0, \dots, rp - 1\}$. Consider a
deck of $p$ piles of $r$ cards. Card $a$ of pile $b$, at position $br + a$, goes to position
$ap + b$. -/
def finPerfectShuffle (p r : ℕ) : Fin (p * r) ≃ Fin (r * p) :=
  finProdFinEquiv.symm.trans ((Equiv.prodComm (Fin p) (Fin r)).trans finProdFinEquiv)

/-- The perfect-shuffle index map sends position $br + a$ to position $ap + b$, for $0 \le b < p$
and $0 \le a < r$. -/
@[simp]
theorem finPerfectShuffle_apply (p r : ℕ) (b : Fin p) (a : Fin r) :
    finPerfectShuffle p r (finProdFinEquiv (b, a)) = finProdFinEquiv (a, b) := by
  simp [finPerfectShuffle]

/-- The inverse of the mod-$p$ perfect-shuffle index map is the mod-$r$ perfect-shuffle index map.
-/
@[simp]
theorem finPerfectShuffle_symm (p r : ℕ) :
    (finPerfectShuffle p r).symm = finPerfectShuffle r p := by
  refine Equiv.ext fun x => ?_
  obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective x
  rw [Equiv.symm_apply_eq, finPerfectShuffle_apply, finPerfectShuffle_apply]

section Basic

variable [Zero R] [One R]

/-- The mod-$p$ **perfect shuffle** $\Pi_{p,r}$. The deck $x \in R^{pr}$ is cut into $p$ piles of
$r$ cards and reassembled by taking one card from each pile in turn, so that $$(\Pi_{p,r}
x)_{ap + b} = x_{br + a} \qquad (0 \le a < r,\ 0 \le b < p).$$

The matrix has the type `Matrix (Fin (r * p)) (Fin (p * r)) R`. It is the matrix of the inverse
of the index map `Matrix.finPerfectShuffle p r`. -/
def perfectShuffle (p r : ℕ) : Matrix (Fin (r * p)) (Fin (p * r)) R :=
  (finPerfectShuffle p r).symm.toPEquiv.toMatrix

/-- The transpose of the perfect shuffle is $\Pi_{p,r}^T = \Pi_{r,p}$. -/
@[simp]
theorem transpose_perfectShuffle (p r : ℕ) :
    (perfectShuffle p r : Matrix (Fin (r * p)) (Fin (p * r)) R)ᵀ = perfectShuffle r p := by
  rw [perfectShuffle, perfectShuffle, ← PEquiv.toMatrix_symm, ← Equiv.toPEquiv_symm,
    Equiv.symm_symm, finPerfectShuffle_symm]

end Basic

variable [NonAssocSemiring R]

/-- The perfect shuffle permutes the entries of a vector: $\Pi_{p,r} x = x \circ \sigma^{-1}$, where
$\sigma$ is the index map `Matrix.finPerfectShuffle p r`. -/
theorem perfectShuffle_mulVec (p r : ℕ) (x : Fin (p * r) → R) :
    perfectShuffle p r *ᵥ x = x ∘ (finPerfectShuffle p r).symm :=
  PEquiv.toMatrix_toPEquiv_mulVec (finPerfectShuffle p r).symm x

/-- The perfect shuffle on a vector, entrywise: $(\Pi_{p,r} x)_{ap + b} = x_{br + a}$ for
$0 \le a < r$ and $0 \le b < p$. -/
@[simp]
theorem perfectShuffle_mulVec_apply (p r : ℕ) (x : Fin (p * r) → R) (b : Fin p) (a : Fin r) :
    (perfectShuffle p r *ᵥ x) (finProdFinEquiv (a, b)) = x (finProdFinEquiv (b, a)) := by
  rw [perfectShuffle_mulVec, Function.comp_apply, finPerfectShuffle_symm, finPerfectShuffle_apply]

/-- The perfect shuffle satisfies both $\Pi_{p,r} \Pi_{p,r}^T = I$ and $\Pi_{p,r}^T \Pi_{p,r} = I$.
-/
private theorem perfectShuffle_orthogonal (p r : ℕ) :
    (perfectShuffle p r : Matrix (Fin (r * p)) (Fin (p * r)) R) *
        (perfectShuffle p r : Matrix (Fin (r * p)) (Fin (p * r)) R)ᵀ = 1 ∧
      (perfectShuffle p r : Matrix (Fin (r * p)) (Fin (p * r)) R)ᵀ *
        (perfectShuffle p r : Matrix (Fin (r * p)) (Fin (p * r)) R) = 1 := by
  rw [transpose_perfectShuffle, perfectShuffle, perfectShuffle, ← PEquiv.toMatrix_trans,
    ← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, ← Equiv.toPEquiv_trans,
    finPerfectShuffle_symm, finPerfectShuffle_symm, ← finPerfectShuffle_symm r p,
    Equiv.symm_trans_self, Equiv.self_trans_symm, Equiv.toPEquiv_refl, Equiv.toPEquiv_refl,
    PEquiv.toMatrix_refl, PEquiv.toMatrix_refl]
  exact ⟨rfl, rfl⟩

/-- The perfect shuffle is orthogonal: $\Pi_{p,r} \Pi_{p,r}^T = I$. -/
theorem perfectShuffle_mul_transpose (p r : ℕ) :
    (perfectShuffle p r : Matrix (Fin (r * p)) (Fin (p * r)) R) *
        (perfectShuffle p r : Matrix (Fin (r * p)) (Fin (p * r)) R)ᵀ = 1 :=
  (perfectShuffle_orthogonal p r).1

/-- The perfect shuffle is orthogonal: $\Pi_{p,r}^T \Pi_{p,r} = I$. -/
theorem transpose_mul_perfectShuffle (p r : ℕ) :
    (perfectShuffle p r : Matrix (Fin (r * p)) (Fin (p * r)) R)ᵀ *
        (perfectShuffle p r : Matrix (Fin (r * p)) (Fin (p * r)) R) = 1 :=
  (perfectShuffle_orthogonal p r).2

end PerfectShuffle

/-! ### The $\varphi$-cyclic shift -/

section CyclicShift

section Basic

variable [Zero R] [One R]

/-- The **$\varphi$-cyclic shift** $Z_\varphi \in R^{n \times n}$ has ones on the subdiagonal,
$\varphi$ in the top right corner, and zeros elsewhere: $(Z_\varphi)_{ij} = 1$ if $i = j + 1$,
$(Z_\varphi)_{0, n-1} = \varphi$, and all other entries are $0$. So $Z_1$ is the downshift and
$Z_0$ is the lower shift. -/
def cyclicShift (n : ℕ) (φ : R) : Matrix (Fin n) (Fin n) R :=
  of fun i j => if (i : ℕ) = j + 1 then 1 else if (i : ℕ) = 0 ∧ (j : ℕ) + 1 = n then φ else 0

/-- The entries of the $\varphi$-cyclic shift: $(Z_\varphi)_{ij}$ is $1$ if $i = j + 1$, $\varphi$
if $i = 0$ and $j = n - 1$, and $0$ otherwise. -/
theorem cyclicShift_apply (n : ℕ) (φ : R) (i j : Fin n) :
    cyclicShift n φ i j
      = if (i : ℕ) = j + 1 then 1 else if (i : ℕ) = 0 ∧ (j : ℕ) + 1 = n then φ else 0 := rfl

/-- The $1$-cyclic shift is the downshift: $Z_1 = \mathcal{D}_n$. -/
theorem cyclicShift_one (n : ℕ) : cyclicShift n (1 : R) = downshift n := by
  ext i j
  rw [cyclicShift_apply, downshift_apply]
  rcases n with _ | n
  · exact i.elim0
  have key : finRotate (n + 1) j = i ↔ (i : ℕ) = j + 1 ∨ ((i : ℕ) = 0 ∧ (j : ℕ) + 1 = n + 1) := by
    rw [Fin.ext_iff, coe_finRotate]
    split_ifs with h
    · rw [Fin.ext_iff, Fin.val_last] at h
      omega
    · rw [Fin.ext_iff, Fin.val_last] at h
      omega
  by_cases h1 : (i : ℕ) = j + 1
  · rw [ite_eq_left h1, ite_eq_left (key.2 (Or.inl h1))]
  · by_cases h2 : (i : ℕ) = 0 ∧ (j : ℕ) + 1 = n + 1
    · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_left (key.2 (Or.inr h2))]
    · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right fun h => (key.1 h).elim h1 h2]

end Basic

variable [Semiring R]

/-- The $\varphi$-cyclic shift moves a vector down one place and multiplies the wrapped-around
component by $\varphi$: $(Z_\varphi x)_0 = \varphi x_{n-1}$, and $(Z_\varphi x)_i = x_{i-1}$ for
$i \ge 1$. -/
theorem cyclicShift_mulVec_apply {n : ℕ} (φ : R) (x : Fin n → R) (i : Fin n) :
    (cyclicShift n φ *ᵥ x) i
      = if h : (i : ℕ) = 0 then φ * x ⟨n - 1, by omega⟩ else x ⟨i - 1, by omega⟩ := by
  have hi := i.is_lt
  rw [mulVec, dotProduct]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨n - 1, by omega⟩]
    · have h1 : ¬ (i : ℕ) = n - 1 + 1 := by omega
      have h2 : (i : ℕ) = 0 ∧ n - 1 + 1 = n := by omega
      rw [cyclicShift_apply, ite_eq_right h1, ite_eq_left h2]
    · intro j _ hj
      have hj' : (j : ℕ) ≠ n - 1 := fun h' => hj (Fin.ext h')
      have h1 : ¬ (i : ℕ) = j + 1 := by omega
      have h2 : ¬ ((i : ℕ) = 0 ∧ (j : ℕ) + 1 = n) := by omega
      rw [cyclicShift_apply, ite_eq_right h1, ite_eq_right h2, zero_mul]
    · simp
  · rw [Finset.sum_eq_single ⟨i - 1, by omega⟩]
    · have h1 : (i : ℕ) = i - 1 + 1 := by omega
      rw [cyclicShift_apply, ite_eq_left h1, one_mul]
    · intro j _ hj
      have hj' : (j : ℕ) ≠ i - 1 := fun h' => hj (Fin.ext h')
      have h1 : ¬ (i : ℕ) = j + 1 := by omega
      have h2 : ¬ ((i : ℕ) = 0 ∧ (j : ℕ) + 1 = n) := by omega
      rw [cyclicShift_apply, ite_eq_right h1, ite_eq_right h2, zero_mul]
    · simp

/-- The powers of $Z_\varphi$ on a vector. Let $k \le n$. Then $(Z_\varphi^k x)_i = x_{i-k}$ if
$k \le i$, and $(Z_\varphi^k x)_i = \varphi\, x_{i+n-k}$ if $i < k$. -/
theorem cyclicShift_pow_mulVec_apply {n : ℕ} (φ : R) (x : Fin n → R) {k : ℕ} (hk : k ≤ n)
    (i : Fin n) :
    (cyclicShift n φ ^ k *ᵥ x) i
      = if h : k ≤ i then x ⟨i - k, by omega⟩ else φ * x ⟨i + n - k, by omega⟩ := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← mulVec_mulVec, cyclicShift_mulVec_apply]
    split_ifs with h0 h1 h1
    · omega
    · rw [ih (by omega)]
      split_ifs with h2
      · congr 2
        ext
        simp only
        omega
      · simp only at h2
        omega
    · rw [ih (by omega)]
      split_ifs with h2
      · congr 1
        ext
        simp only
        omega
      · simp only at h2
        omega
    · rw [ih (by omega)]
      split_ifs with h2
      · simp only at h2
        omega
      · congr 2
        ext
        simp only
        omega

/-- Let $A \in R^{n \times n}$ and let $i \ge 1$. Then $(Z_\varphi A)_{ij} = a_{i-1, j}$ for every
$j$. -/
theorem cyclicShift_mul_apply_of_pos {n : ℕ} (φ : R) (A : Matrix (Fin n) (Fin n) R)
    {i : Fin n} (hi : 0 < (i : ℕ)) (j : Fin n) :
    (cyclicShift n φ * A) i j = A ⟨i - 1, by omega⟩ j := by
  have := cyclicShift_mulVec_apply φ (fun l => A l j) i
  rw [dite_eq_right (by omega)] at this
  exact this

/-- Let $A \in R^{n \times n}$ and let $j + 1 < n$. Then $(A Z_\varphi)_{ij} = a_{i, j+1}$ for every
$i$. -/
theorem mul_cyclicShift_apply_of_lt {n : ℕ} (φ : R) (A : Matrix (Fin n) (Fin n) R) (i : Fin n)
    {j : Fin n} (hj : (j : ℕ) + 1 < n) :
    (A * cyclicShift n φ) i j = A i ⟨j + 1, hj⟩ := by
  rw [Matrix.mul_apply, Finset.sum_eq_single ⟨j + 1, hj⟩]
  · rw [cyclicShift_apply, ite_eq_left rfl, mul_one]
  · intro l _ hl
    have hl' : (l : ℕ) ≠ j + 1 := fun h' => hl (Fin.ext h')
    rw [cyclicShift_apply, ite_eq_right hl', ite_eq_right (by omega), mul_zero]
  · simp

/-- Let $A \in R^{n \times n}$ and let $j \ge 1$. Then $(A Z_\varphi^T)_{ij} = a_{i, j-1}$ for every
$i$. -/
theorem mul_transpose_cyclicShift_apply_of_pos {n : ℕ} (φ : R) (A : Matrix (Fin n) (Fin n) R)
    (i : Fin n) {j : Fin n} (hj : 0 < (j : ℕ)) :
    (A * (cyclicShift n φ)ᵀ) i j = A i ⟨j - 1, by omega⟩ := by
  rw [Matrix.mul_apply, Finset.sum_eq_single ⟨j - 1, by omega⟩]
  · rw [transpose_apply, cyclicShift_apply, ite_eq_left (by simp only; omega), mul_one]
  · intro l _ hl
    have hl' : (j : ℕ) ≠ l + 1 := fun h' => hl (Fin.ext (by simp only; omega))
    rw [transpose_apply, cyclicShift_apply, ite_eq_right hl', ite_eq_right (by omega), mul_zero]
  · simp

/-- Let $A \in R^{n \times n}$ and let $i + 1 < n$. Then $(Z_\varphi^T A)_{ij} = a_{i+1, j}$ for
every $j$. -/
theorem transpose_cyclicShift_mul_apply_of_lt {n : ℕ} (φ : R) (A : Matrix (Fin n) (Fin n) R)
    {i : Fin n} (hi : (i : ℕ) + 1 < n) (j : Fin n) :
    ((cyclicShift n φ)ᵀ * A) i j = A ⟨i + 1, hi⟩ j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single ⟨i + 1, hi⟩]
  · rw [transpose_apply, cyclicShift_apply, ite_eq_left rfl, one_mul]
  · intro l _ hl
    have hl' : (l : ℕ) ≠ i + 1 := fun h' => hl (Fin.ext h')
    rw [transpose_apply, cyclicShift_apply, ite_eq_right hl', ite_eq_right (by omega), zero_mul]
  · simp

/-- The $\varphi$-cyclic shift satisfies $Z_\varphi^n = \varphi I$: one pass around the cycle
multiplies every component by $\varphi$. -/
theorem cyclicShift_pow_card (n : ℕ) (φ : R) : cyclicShift n φ ^ n = φ • (1 : Matrix _ _ R) := by
  refine ext_of_mulVec_single fun j => funext fun i => ?_
  have hi : ¬ n ≤ (i : ℕ) := by have := i.is_lt; omega
  rw [cyclicShift_pow_mulVec_apply φ _ le_rfl, dite_eq_right hi, smul_mulVec, one_mulVec]
  simp only [Nat.add_sub_cancel, Fin.eta, Pi.smul_apply, smul_eq_mul]

end CyclicShift

end Matrix
