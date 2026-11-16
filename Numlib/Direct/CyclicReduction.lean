/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.BlockTridiagonal

/-!
# Block cyclic reduction

Block cyclic reduction, due to Buzbee, Golub and Nielson, solves a block tridiagonal system with
constant commuting blocks, as in [golub2013matrix], §4.5.3. Let $K$ be a commutative ring, and let
$D, F \in K^{q \times q}$ satisfy $DF = FD$. The system (4.5.9) for the unknowns
$x_1, \dots, x_N \in K^q$ is
$$D x_1 + F x_2 = b_1, \qquad F x_{i-1} + D x_i + F x_{i+1} = b_i \quad (1 < i < N), \qquad F
  x_{N-1} + D x_N = b_N.$$
The discrete Poisson matrix of §4.8.4 is the case $D = \mathcal{T}^{(DD)} + 2I$, $F = -I$.

One reduction step eliminates every other unknown. Multiply three consecutive equations by $F$, $-D$
and $F$ and add them: the result is a system of the same shape for the unknowns $x_1, x_3, \dots$
(indexed from $0$), with the blocks $D^{(1)} = 2F^2 - D^2$ and $F^{(1)} = F^2$, which commute again.
The eliminated unknowns $x_0, x_2, \dots$ (the odd-numbered unknowns of the book) are recovered from
$q \times q$ systems with the matrix $D$. For $N = 2^k - 1$ unknowns the reduction can be repeated
until a single $q \times q$ system for the middle unknown is left.

## Main definitions

* `CyclicReduction.extend`: the zero extension $\tilde x$ of a block vector to all integer indices.
* `CyclicReduction.constBlockTridiagonal`: the operator $(Tx)_i = D x_i + F \tilde x_{i-1} + F
  \tilde x_{i+1}$ of (4.5.9).
* `CyclicReduction.reducedDiag`, `CyclicReduction.reducedOff`, `CyclicReduction.reducedRhs`: the
  blocks $2F^2 - D^2$ and $F^2$ and the right-hand side after one reduction step.
* `CyclicReduction.size`: the sizes $2^k - 1$, as the recursion $s_0 = 0$, $s_{k+1} = 2 s_k + 1$.

## Main results

* `CyclicReduction.constBlockTridiagonal_eq_blockTridiagonal_mulVec`: the operator is the block
  tridiagonal matrix with diagonal blocks $D$ and off-diagonal blocks $F$.
* `CyclicReduction.commute_reduced`: the reduced blocks commute.
* `CyclicReduction.constBlockTridiagonal_reduce`: one reduction step.
* `CyclicReduction.constBlockTridiagonal_even_eq`: the eliminated unknowns solve $q \times q$
  systems with the matrix $D$.
* `CyclicReduction.constBlockTridiagonal_iterate_reduce`: after $k$ steps on $2^{k+1} - 1$ unknowns,
  the middle unknown solves one $q \times q$ system.

## Implementation notes

* Unknowns are indexed from $0$: a block vector is `x : Fin N → Fin q → K`, with the blocks
  $x_0, \dots, x_{N-1}$.
* The operator is written directly on block vectors. The missing neighbours of the first and the
  last unknown are read as zero through the zero extension
  `CyclicReduction.extend x : ℤ → Fin q → K`, so that no boundary case is special. The operator is
  the block tridiagonal matrix `Matrix.blockTridiagonal` of
  `Numlib.LinearAlgebra.Matrix.BlockTridiagonal` applied to the flattened vector.
* The sizes $2^k - 1$ are given by the recursion `CyclicReduction.size (k + 1) = 2 *
  CyclicReduction.size k + 1`, so that one reduction step maps a system of size
  `CyclicReduction.size (k + 1)` to one of size `CyclicReduction.size k` with no cast.
* The stabilized variant of Buneman and the operation counts are not formalized.
-/

open Matrix

namespace CyclicReduction

variable {K : Type*} [CommRing K] {q N M : ℕ}

/-! ### The operator -/

/-- The **zero extension** of a block vector $x = (x_0, \dots, x_{N-1})$, $x_i \in K^q$, to all
integer indices: $\tilde x_i = x_i$ for $0 \le i < N$, and $\tilde x_i = 0$ otherwise. -/
def extend (x : Fin N → Fin q → K) (i : ℤ) : Fin q → K :=
  if h : 0 ≤ i ∧ i < N then x ⟨i.toNat, by omega⟩ else 0

/-- For an integer $i$ with $0 \le i < N$, the zero extension satisfies $\tilde x_i = x_i$. -/
theorem extend_of_lt (x : Fin N → Fin q → K) {i : ℤ} (h₀ : 0 ≤ i) (h : i < N) :
    extend x i = x ⟨i.toNat, by omega⟩ := dite_eq_left ⟨h₀, h⟩

/-- For an index $i \in \{0, \dots, N - 1\}$, the zero extension satisfies $\tilde x_i = x_i$. -/
@[simp]
theorem extend_coe (x : Fin N → Fin q → K) (i : Fin N) : extend x (i : ℕ) = x i := by
  rw [extend_of_lt x (by omega) (by exact_mod_cast i.isLt)]
  congr

/-- The zero extension vanishes at negative indices: $\tilde x_i = 0$ for $i < 0$. -/
theorem extend_of_neg (x : Fin N → Fin q → K) {i : ℤ} (h : i < 0) : extend x i = 0 :=
  dite_eq_right (by omega)

/-- The zero extension vanishes from index $N$ on: $\tilde x_i = 0$ for $i \ge N$. -/
theorem extend_of_le (x : Fin N → Fin q → K) {i : ℤ} (h : (N : ℤ) ≤ i) : extend x i = 0 :=
  dite_eq_right (by omega)

/-- The zero extension commutes with multiplication of the blocks by a matrix: for
$A \in K^{q \times q}$, the zero extension of $(A x_j)_j$ at $i$ is $A \tilde x_i$, for every
integer $i$. -/
theorem extend_mulVec (A : Matrix (Fin q) (Fin q) K) (x : Fin N → Fin q → K) (i : ℤ) :
    extend (fun j => A *ᵥ x j) i = A *ᵥ extend x i := by
  unfold extend
  split_ifs <;> simp

/-- The **constant-block tridiagonal operator** of [golub2013matrix] (4.5.9). For
$D, F \in K^{q \times q}$ and a block vector $x = (x_0, \dots, x_{N-1})$, it is
$$(Tx)_i = D x_i + F \tilde x_{i-1} + F \tilde x_{i+1}, \qquad 0 \le i < N,$$
where $\tilde x$ is the zero extension, so that the missing neighbours at the two ends are zero. -/
def constBlockTridiagonal (D F : Matrix (Fin q) (Fin q) K) (x : Fin N → Fin q → K) (i : Fin N) :
    Fin q → K :=
  D *ᵥ x i + F *ᵥ extend x ((i : ℕ) - 1) + F *ᵥ extend x ((i : ℕ) + 1)

/-- The system $Tx = b$ of `CyclicReduction.constBlockTridiagonal`, read on the zero extensions:
$Tx = b$ if and only if, for every integer $i$ with $0 \le i < N$,
$$D \tilde x_i + F \tilde x_{i-1} + F \tilde x_{i+1} = \tilde b_i.$$
-/
theorem constBlockTridiagonal_eq_iff {D F : Matrix (Fin q) (Fin q) K}
    {x b : Fin N → Fin q → K} :
    constBlockTridiagonal D F x = b ↔ ∀ i : ℤ, 0 ≤ i → i < N →
      D *ᵥ extend x i + F *ᵥ extend x (i - 1) + F *ᵥ extend x (i + 1) = extend b i := by
  constructor
  · rintro rfl i h₀ h
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h₀
    have hn : n < N := by omega
    have := extend_coe (constBlockTridiagonal D F x) ⟨n, hn⟩
    simp only at this
    rw [this, constBlockTridiagonal]
    exact congrArg (fun v => D *ᵥ v + F *ᵥ extend x (n - 1) + F *ᵥ extend x (n + 1))
      (extend_coe x ⟨n, hn⟩)
  · intro h
    funext i
    have := h (i : ℕ) (by omega) (by exact_mod_cast i.isLt)
    rwa [extend_coe, extend_coe] at this

/-- For a block vector $v$ with the indices $0, \dots, N$, the sum of the $v_j$ with $j + 1 = i$ is
$\tilde v_{i-1}$. -/
private theorem sum_ite_succ_eq (v : Fin (N + 1) → Fin q → K) (i : Fin (N + 1)) :
    ∑ j : Fin (N + 1), (if (j : ℕ) + 1 = i then v j else 0) = extend v ((i : ℕ) - 1) := by
  have := sum_dite_val_add_one_eq i (fun j (_ : (j : ℕ) + 1 = i) => v j)
  simp only [dite_eq_ite] at this
  rw [this]
  split_ifs with h
  · rw [extend_of_lt v (by omega) (by omega)]
    congr
    omega
  · rw [extend_of_neg v (by omega)]

/-- For a block vector $v$ with the indices $0, \dots, N$, the sum of the $v_j$ with $j = i + 1$ is
$\tilde v_{i+1}$. -/
private theorem sum_ite_eq_succ (v : Fin (N + 1) → Fin q → K) (i : Fin (N + 1)) :
    ∑ j : Fin (N + 1), (if (j : ℕ) = i + 1 then v j else 0) = extend v ((i : ℕ) + 1) := by
  have := sum_dite_val_eq_add_one i (fun j (_ : (j : ℕ) = i + 1) => v j)
  simp only [dite_eq_ite] at this
  rw [this]
  split_ifs with h
  · rw [extend_of_lt v (by omega) (by omega)]
    congr
  · rw [extend_of_le v (by omega)]

/-- **Block tridiagonal form.** Let $D, F \in K^{q \times q}$, and let $x$ be a block vector with
$N + 1$ blocks. Then `CyclicReduction.constBlockTridiagonal D F x` is the product of the block
tridiagonal matrix with diagonal blocks $D$ and off-diagonal blocks $F$ and the flattened vector
of $x$: the entry $k$ of block $i$ of the two agree, for all $i$ and $k$.

The block tridiagonal matrix is `Matrix.blockTridiagonal`, and the flattened vector is indexed
by the pairs $(i, k)$. -/
theorem constBlockTridiagonal_eq_blockTridiagonal_mulVec (D F : Matrix (Fin q) (Fin q) K)
    (x : Fin (N + 1) → Fin q → K) (i : Fin (N + 1)) (k : Fin q) :
    (blockTridiagonal (fun _ => F) (fun _ => D) (fun _ => F) *ᵥ fun p => x p.1 p.2) (i, k) =
      constBlockTridiagonal D F x i k := by
  have hsum : (blockTridiagonal (fun _ => F) (fun _ => D) (fun _ => F) *ᵥ
      fun p => x p.1 p.2) (i, k) =
      (∑ j : Fin (N + 1), tridiagonalOf (fun _ : Fin N => F) (fun _ => D) (fun _ => F) i j *ᵥ
        x j) k := by
    simp only [mulVec, dotProduct, Fintype.sum_prod_type, blockTridiagonal_apply,
      Finset.sum_apply]
  have hterm : ∀ j : Fin (N + 1),
      tridiagonalOf (fun _ : Fin N => F) (fun _ => D) (fun _ => F) i j *ᵥ x j =
        (if i = j then D *ᵥ x j else 0) +
        (if (j : ℕ) + 1 = i then F *ᵥ x j else 0) +
        (if (j : ℕ) = i + 1 then F *ᵥ x j else 0) := by
    intro j
    by_cases hij : i = j
    · subst hij
      simp
    · have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
      simp only [tridiagonalOf, of_apply, hij', ite_false, hij]
      split_ifs <;> first | omega | simp
  rw [hsum, Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib,
    Finset.sum_add_distrib, sum_ite_succ_eq (fun j => F *ᵥ x j),
    sum_ite_eq_succ (fun j => F *ᵥ x j), extend_mulVec, extend_mulVec]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rfl

/-! ### One reduction step -/

/-- The diagonal block after one reduction step, $D^{(1)} = 2F^2 - D^2$ ([golub2013matrix], §4.5.3).
-/
def reducedDiag (D F : Matrix (Fin q) (Fin q) K) : Matrix (Fin q) (Fin q) K :=
  2 • (F * F) - D * D

/-- The off-diagonal block after one reduction step, $F^{(1)} = F^2$ ([golub2013matrix], §4.5.3). -/
def reducedOff (F : Matrix (Fin q) (Fin q) K) : Matrix (Fin q) (Fin q) K :=
  F * F

/-- The right-hand side after one reduction step. For a block vector $b$ with $2M + 1$ blocks,
indexed from $0$, it is the block vector with $M$ blocks
$$b^{(1)}_j = F (b_{2j} + b_{2j+2}) - D b_{2j+1}, \qquad 0 \le j < M.$$
-/
def reducedRhs (D F : Matrix (Fin q) (Fin q) K) (b : Fin (2 * M + 1) → Fin q → K) (j : Fin M) :
    Fin q → K :=
  F *ᵥ (b ⟨2 * j, by omega⟩ + b ⟨2 * j + 2, by omega⟩) - D *ᵥ b ⟨2 * j + 1, by omega⟩

/-- **The reduced blocks commute** ([golub2013matrix], §4.5.3). Let $D, F \in K^{q \times q}$
satisfy $DF = FD$. Then $D^{(1)} = 2F^2 - D^2$ and $F^{(1)} = F^2$ satisfy
$D^{(1)} F^{(1)} = F^{(1)} D^{(1)}$, so the reduction can be repeated. -/
theorem commute_reduced {D F : Matrix (Fin q) (Fin q) K} (h : D * F = F * D) :
    reducedDiag D F * reducedOff F = reducedOff F * reducedDiag D F := by
  have h' : D * (F * F) = F * F * D := by
    rw [← Matrix.mul_assoc, h, Matrix.mul_assoc, h, Matrix.mul_assoc]
  have h'' : D * (D * (F * F)) = F * (F * (D * D)) := by
    rw [h', ← Matrix.mul_assoc, h', Matrix.mul_assoc, Matrix.mul_assoc]
  simp only [reducedDiag, reducedOff, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.mul_assoc]
  rw [h'']

/-- Let $x$ be a block vector with $2M + 1$ blocks, indexed from $0$, and let $x'_j = x_{2j+1}$ for
$0 \le j < M$. Then the zero extensions satisfy $\tilde x'_j = \tilde x_{2j+1}$ for every
integer $j$. -/
theorem extend_odd (x : Fin (2 * M + 1) → Fin q → K) (j : ℤ) :
    extend (fun j : Fin M => x ⟨2 * j + 1, by omega⟩) j = extend x (2 * j + 1) := by
  unfold extend
  split_ifs with h₁ h₂ h₂
  · refine congrArg x (Fin.ext ?_)
    change 2 * j.toNat + 1 = (2 * j + 1).toNat
    omega
  · exfalso; omega
  · exfalso; omega
  · rfl

/-- **One cyclic reduction step** ([golub2013matrix], §4.5.3). Let $D, F \in K^{q \times q}$ satisfy
$DF = FD$, and let $x$ and $b$ be block vectors with $2M + 1$ blocks, indexed from $0$, with
$Tx = b$ for the operator $T$ with the blocks $D$ and $F$. Then the odd-indexed unknowns
$x'_j = x_{2j+1}$, $0 \le j < M$, solve the system with the blocks $D^{(1)} = 2F^2 - D^2$ and
$F^{(1)} = F^2$ and the right-hand side
$$b^{(1)}_j = F (b_{2j} + b_{2j+2}) - D b_{2j+1}.$$
-/
theorem constBlockTridiagonal_reduce {D F : Matrix (Fin q) (Fin q) K} (hDF : D * F = F * D)
    {x b : Fin (2 * M + 1) → Fin q → K} (h : constBlockTridiagonal D F x = b) :
    constBlockTridiagonal (reducedDiag D F) (reducedOff F)
      (fun j : Fin M => x ⟨2 * j + 1, by omega⟩) = reducedRhs D F b := by
  rw [constBlockTridiagonal_eq_iff] at h ⊢
  intro j h₀ hj
  simp only [extend_odd]
  have e0 := h (2 * j) (by omega) (by push_cast; omega)
  have e1 := h (2 * j + 1) (by omega) (by push_cast; omega)
  have e2 := h (2 * j + 2) (by omega) (by push_cast; omega)
  rw [show 2 * j + 1 - 1 = 2 * j by ring, show 2 * j + 1 + 1 = 2 * j + 2 by ring] at e1
  rw [show 2 * j + 2 - 1 = 2 * j + 1 by ring, show 2 * j + 2 + 1 = 2 * j + 3 by ring] at e2
  rw [show 2 * (j - 1) + 1 = 2 * j - 1 by ring, show 2 * (j + 1) + 1 = 2 * j + 3 by ring]
  have hb : extend (reducedRhs D F b) j =
      F *ᵥ (extend b (2 * j) + extend b (2 * j + 2)) - D *ᵥ extend b (2 * j + 1) := by
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h₀
    have hn : n < M := by omega
    have := extend_coe (reducedRhs D F b) ⟨n, hn⟩
    simp only at this
    rw [this, reducedRhs]
    have c0 := extend_coe b ⟨2 * n, by omega⟩
    have c1 := extend_coe b ⟨2 * n + 1, by omega⟩
    have c2 := extend_coe b ⟨2 * n + 2, by omega⟩
    push_cast at c0 c1 c2
    rw [c0, c1, c2]
  rw [hb, ← e0, ← e1, ← e2]
  simp only [reducedDiag, reducedOff, mulVec_add, sub_mulVec, mulVec_mulVec, smul_mulVec, hDF]
  abel

/-- **The back substitution of cyclic reduction** ([golub2013matrix], §4.5.3). Let
$D, F \in K^{q \times q}$, and let $x$ and $b$ be block vectors with $2M + 1$ blocks, indexed
from $0$, with $Tx = b$. Then for every $j$ with $0 \le j \le M$, the even-indexed unknown
$x_{2j}$ solves the $q \times q$ system
$$D x_{2j} = b_{2j} - F (\tilde x_{2j-1} + \tilde x_{2j+1}),$$
where the zero extension $\tilde x$ makes the neighbours out of range zero.

This result does not need $DF = FD$. -/
theorem constBlockTridiagonal_even_eq {D F : Matrix (Fin q) (Fin q) K}
    {x b : Fin (2 * M + 1) → Fin q → K} (h : constBlockTridiagonal D F x = b) (j : Fin (M + 1)) :
    D *ᵥ x ⟨2 * j, by omega⟩ =
      b ⟨2 * j, by omega⟩ - F *ᵥ (extend x (2 * (j : ℕ) - 1) + extend x (2 * (j : ℕ) + 1)) := by
  rw [← h, constBlockTridiagonal, mulVec_add]
  push_cast
  abel

/-! ### Iterated reduction -/

/-- The sizes of the systems that reduce down to one unknown: $s_0 = 0$ and $s_{k+1} = 2 s_k + 1$,
so that $s_k = 2^k - 1$. -/
def size : ℕ → ℕ
  | 0 => 0
  | k + 1 => 2 * size k + 1

/-- The sizes satisfy $s_k = 2^k - 1$. -/
theorem size_eq (k : ℕ) : size k = 2 ^ k - 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [size, ih, pow_succ]
    have := Nat.one_le_two_pow (n := k)
    omega

/-- The diagonal block after $k$ reduction steps. Put $(D_0, F_0) = (D, F)$ and
$(D_{p+1}, F_{p+1}) = (2F_p^2 - D_p^2, F_p^2)$; the value is $D_k$. -/
def diagIter : ℕ → Matrix (Fin q) (Fin q) K → Matrix (Fin q) (Fin q) K →
    Matrix (Fin q) (Fin q) K
  | 0, D, _ => D
  | k + 1, D, F => diagIter k (reducedDiag D F) (reducedOff F)

/-- The right-hand side after $k$ reduction steps of a system with $s_{k+1} = 2^{k+1} - 1$ unknowns.
After $k$ steps one unknown is left, and the value is the right-hand side $b_k \in K^q$ of its
single $q \times q$ system. For $k = 0$ the system has one unknown, and the value is the single
block of $b$. For $k + 1$ it is the value for $k$ applied to the blocks $D^{(1)}$, $F^{(1)}$ and
the right-hand side $b^{(1)}$ of one reduction step. -/
def rhsIter : (k : ℕ) → Matrix (Fin q) (Fin q) K → Matrix (Fin q) (Fin q) K →
    (Fin (size (k + 1)) → Fin q → K) → Fin q → K
  | 0, _, _, b => b ⟨0, by simp [size]⟩
  | k + 1, D, F, b =>
    rhsIter k (reducedDiag D F) (reducedOff F) (reducedRhs (M := size (k + 1)) D F b)

/-- **Iterated cyclic reduction** ([golub2013matrix], §4.5.3). Let $D, F \in K^{q \times q}$ satisfy
$DF = FD$, and let $x$ and $b$ be block vectors with $N = 2^{k+1} - 1$ blocks, indexed from $0$,
with $Tx = b$. Then after $k$ reduction steps, the middle unknown $x_{2^k - 1}$ solves the
single $q \times q$ system
$$D_k x_{2^k - 1} = b_k,$$
where $(D_0, F_0) = (D, F)$, $(D_{p+1}, F_{p+1}) = (2F_p^2 - D_p^2, F_p^2)$, and $b_k$ is the
right-hand side after $k$ reduction steps. The book says: "we are left with a single
$q \times q$ system".

The size $N$ is `CyclicReduction.size (k + 1)`, and the middle index $2^k - 1$ is
`CyclicReduction.size k`. The block $D_k$ is `CyclicReduction.diagIter k D F`, and $b_k$ is
`CyclicReduction.rhsIter k D F b`. -/
theorem constBlockTridiagonal_iterate_reduce (k : ℕ) {D F : Matrix (Fin q) (Fin q) K}
    (hDF : D * F = F * D) {x b : Fin (size (k + 1)) → Fin q → K}
    (h : constBlockTridiagonal D F x = b) :
    diagIter k D F *ᵥ x ⟨size k, by simp only [size]; omega⟩ = rhsIter k D F b := by
  induction k generalizing D F with
  | zero =>
    have := congrFun h ⟨0, by simp [size]⟩
    rw [constBlockTridiagonal, extend_of_neg x (by simp),
      extend_of_le x (by simp [size])] at this
    simpa [diagIter, rhsIter, size] using this
  | succ k ih =>
    have hr := constBlockTridiagonal_reduce (M := size (k + 1)) hDF h
    exact ih (commute_reduced hDF) hr

end CyclicReduction
