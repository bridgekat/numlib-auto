/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Vandermonde
import Numlib.Approximation.NewtonForm

/-!
# Vandermonde systems and the Björck–Pereyra factorization

Let $x_0, \dots, x_n$ be nodes in a field $K$. The Vandermonde matrix $V = V(x_0, \dots, x_n)$ of
[golub2013matrix] §4.6 has the entries $v_{ij} = x_j^i$, and the Vandermonde system $V^T a = f$ asks
for the coefficients $a$ of the polynomial $p(t) = \sum_j a_j t^j$ with $p(x_i) = f_i$. This module
proves the factorization of Björck and Pereyra (1970), which solves this system for distinct nodes
by two sweeps of elementary matrices; see also [higham2002accuracy] §22.2.

The sweeps are products of the elementary lower bidiagonal matrices $L_k(\alpha)$, the identity with
$-\alpha$ on the subdiagonal from column $k$ on, and of diagonal matrices $D_k$ of node differences.
The divided-difference sweep $c = U^T f$, with $U^T = D_{n-1}^{-1} L_{n-1}(1) \cdots D_0^{-1}
L_0(1)$, computes the coefficients $c_k = f[x_0, \dots, x_k]$ of the Newton form of the interpolant.
The Newton-to-monomial sweep $a = L^T c$, with $L^T = L_0(x_0)^T \cdots L_{n-1}(x_{n-1})^T$,
converts the Newton form to monomial coefficients. Together they give $V^{-T} = L^T U^T$.

## Main definitions

* `BjorckPereyra.lowerBidiag`: the elementary lower bidiagonal matrix $L_k(\alpha)$.
* `BjorckPereyra.lowerFactorT`: the factor $L^T = L_0(x_0)^T \cdots L_{n-1}(x_{n-1})^T$.
* `BjorckPereyra.diffScale`: the diagonal matrix $D_k$ of node differences.
* `BjorckPereyra.upperFactorT`: the factor $U^T = D_{n-1}^{-1} L_{n-1}(1) \cdots D_0^{-1} L_0(1)$.

## Main results

* `Matrix.vandermonde_mulVec_eq_eval`: entry $i$ of $V^T a$ is the value at $x_i$ of the polynomial
  with coefficients $a$ (4.6.1).
* `BjorckPereyra.lowerBidiag_mulVec_apply` and `BjorckPereyra.vecMul_transpose_lowerBidiag_apply`:
  $L_k(\alpha)$, applied to a column vector, and $L_k(\alpha)^T$, applied to a row vector, subtract
  $\alpha$ times the previous entry from each entry after position $k$.
* `BjorckPereyra.pow_vecMul_lowerFactorT`: the row $(1, t, \dots, t^n)$ times $L^T$ is the row of
  Newton basis values $\prod_{l < j} (t - x_l)$.
* `BjorckPereyra.vandermonde_mul_lowerFactorT`: $V^T L^T$ is the Newton basis matrix with entries
  $\prod_{l < j} (x_i - x_l)$.
* `BjorckPereyra.lowerFactorT_mulVec_newtonCoeff`: the polynomial with coefficients $L^T c$ is the
  Newton form with coefficients $c$.
* `BjorckPereyra.inv_diffScale`: for distinct nodes, $D_k^{-1}$ is the diagonal matrix of the
  reciprocals of the diagonal of $D_k$.
* `BjorckPereyra.upperFactorT_mulVec_eq_newtonOn`: for distinct nodes,
  $(U^T f)_k = f[x_0, \dots, x_k]$.
* `BjorckPereyra.inv_vandermonde_eq`: for distinct nodes, $V^{-T} = L^T U^T$.

## Proof outline

The second sweep is proved as a statement about row vectors, uniformly over a commutative ring: the
row of powers $(1, t, \dots, t^n)$ times $L^T$ is the row of Newton basis values
$\bigl(\prod_{l < j} (t - x_l)\bigr)_j$. At $t = x_i$ this gives the product $V^T L^T$, and at
$t = X$ over the polynomial ring it gives the polynomial identity of the Newton-to-monomial
conversion. The first sweep is proved by induction on the number of factors applied. The invariant
is that entry $i$ holds the divided difference over the window $[i - k, i]$ of consecutive nodes,
with the indices in $\mathbb{N}$ and the window truncated at $0$.

## Implementation notes

* Mathlib's `Matrix.vandermonde x : Matrix (Fin (n + 1)) (Fin (n + 1)) K` has the entries $x_i^j$,
  so the nodes index the rows; it is the transpose $V^T$ of the matrix of the book. The
  interpolation system of the book is therefore `vandermonde x *ᵥ a = f`.
* The results on $L_k(\alpha)$ and $L^T$ hold over any commutative ring; the results on $D_k$ and
  $U^T$ need a field.
* The surface library proves Algorithms 4.6.1 and 4.6.2 of [golub2013matrix] from
  `BjorckPereyra.inv_vandermonde_eq`.
-/

open Matrix Polynomial Finset

open scoped Fin.NatCast

/-- Vandermonde systems are interpolation problems. Let $R$ be a commutative ring and let
$x, a \in R^n$. Then entry $i$ of $V^T a$ is the value at $x_i$ of the polynomial with
coefficients $a$: $$(V^T a)_i = p(x_i), \qquad p = \sum_j a_j X^j.$$ This is (4.6.1) of
[golub2013matrix].

The matrix $V^T$ is Mathlib's `Matrix.vandermonde x`, with the entries $x_i^j$. -/
theorem Matrix.vandermonde_mulVec_eq_eval {R : Type*} [CommRing R] {n : ℕ} (x : Fin n → R)
    (a : Fin n → R) (i : Fin n) :
    (vandermonde x *ᵥ a) i = (∑ j, C (a j) * X ^ (j : ℕ)).eval (x i) := by
  simp only [mulVec, dotProduct, vandermonde_apply, eval_finsetSum, eval_mul, eval_C, eval_pow,
    eval_X, mul_comm]

namespace BjorckPereyra

section Ring

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The **elementary lower bidiagonal matrix** $L_k(\alpha)$ of [golub2013matrix] §4.6.2. Let $R$ be
a commutative ring, $n, k \in \mathbb{N}$ and $\alpha \in R$. Then $L_k(\alpha)$ is the
$(n+1) \times (n+1)$ identity matrix with $-\alpha$ in the subdiagonal positions $(i + 1, i)$
for $i \ge k$: $$L_k(\alpha)_{ij} = \begin{cases} 1 & \text{if } i = j, \\ -\alpha & \text{if }
i = j + 1 \text{ and } j \ge k, \\ 0 & \text{otherwise.} \end{cases}$$ For $k \ge n$ it is the
identity matrix. -/
def lowerBidiag (n k : ℕ) (α : R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  of fun i j => if i = j then 1 else if (i : ℕ) = j + 1 ∧ k ≤ (j : ℕ) then -α else 0

/-- Applied to a vector, $L_k(\alpha)$ subtracts $\alpha$ times the previous entry from each entry
after position $k$: for $c \in R^{n+1}$, $(L_k(\alpha) c)_i = c_i - \alpha c_{i-1}$ if
$i \ge k + 1$, and $(L_k(\alpha) c)_i = c_i$ otherwise. -/
theorem lowerBidiag_mulVec_apply (k : ℕ) (α : R) (c : Fin (n + 1) → R) (i : Fin (n + 1)) :
    (lowerBidiag n k α *ᵥ c) i =
      if h : k + 1 ≤ (i : ℕ) then c i - α * c ⟨i - 1, by omega⟩ else c i := by
  simp only [mulVec, dotProduct, lowerBidiag, of_apply]
  split_ifs with h
  · rw [Finset.sum_eq_add i ⟨i - 1, by omega⟩ (fun h' => by simp [Fin.ext_iff] at h'; omega)]
    · have h1 : (i : ℕ) = (i : ℕ) - 1 + 1 ∧ k ≤ (i : ℕ) - 1 := by omega
      have h2 : i ≠ ⟨i - 1, by omega⟩ := fun h' => by simp [Fin.ext_iff] at h'; omega
      simp only [ite_true, one_mul, h2, ite_false]
      rw [ite_eq_left h1]
      ring
    · intro j _ hj
      have h1 : i ≠ j := Ne.symm hj.1
      have h2 : ¬ ((i : ℕ) = j + 1 ∧ k ≤ (j : ℕ)) := fun h' =>
        hj.2 (Fin.ext (by simp only; omega))
      simp [h1, h2]
    · simp
    · simp
  · rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      have h1 : i ≠ j := Ne.symm hj
      have h2 : ¬ ((i : ℕ) = j + 1 ∧ k ≤ (j : ℕ)) := by omega
      simp [h1, h2]
    · simp

/-- Applied to a row vector, $L_k(\alpha)^T$ acts in the same way: for $w \in R^{n+1}$,
$(w^T L_k(\alpha)^T)_j = w_j - \alpha w_{j-1}$ if $j \ge k + 1$, and
$(w^T L_k(\alpha)^T)_j = w_j$ otherwise. -/
theorem vecMul_transpose_lowerBidiag_apply (k : ℕ) (α : R) (w : Fin (n + 1) → R)
    (j : Fin (n + 1)) :
    (w ᵥ* (lowerBidiag n k α)ᵀ) j =
      if h : k + 1 ≤ (j : ℕ) then w j - α * w ⟨j - 1, by omega⟩ else w j := by
  rw [vecMul_transpose, lowerBidiag_mulVec_apply]

/-- The factor $L^T$ of the Newton-to-monomial sweep of [golub2013matrix] §4.6.2. For nodes
$x_0, \dots, x_n$ in a commutative ring, $$L^T = L_0(x_0)^T L_1(x_1)^T \cdots
L_{n-1}(x_{n-1})^T.$$ Its transpose is the unit lower triangular matrix $L$ of the book.

The node $x_n$ is not used. For $n = 0$ the product is empty and $L^T$ is the identity. -/
def lowerFactorT (x : Fin (n + 1) → R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  ((List.range n).map fun k => (lowerBidiag n k (x k))ᵀ).prod

/-- The partial product $L_0(x_0)^T \cdots L_{k-1}(x_{k-1})^T$. -/
private def lowerFactorTPartial (x : Fin (n + 1) → R) (k : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  ((List.range k).map fun k => (lowerBidiag n k (x k))ᵀ).prod

private theorem lowerFactorTPartial_succ (x : Fin (n + 1) → R) (k : ℕ) :
    lowerFactorTPartial x (k + 1) = lowerFactorTPartial x k * (lowerBidiag n k (x k))ᵀ := by
  simp [lowerFactorTPartial, List.range_succ]

/-- After $k \le n$ factors of the second sweep, entry $j$ of the row of powers $(1, t, \dots, t^n)$
is $t^{j - \min(j, k)} \prod_{l < \min(j, k)} (t - x_l)$. -/
private theorem pow_vecMul_lowerFactorTPartial (x : Fin (n + 1) → R) (t : R) {k : ℕ}
    (hk : k ≤ n) (j : Fin (n + 1)) :
    ((fun j : Fin (n + 1) => t ^ (j : ℕ)) ᵥ* lowerFactorTPartial x k) j =
      t ^ ((j : ℕ) - min (j : ℕ) k) * ∏ l ∈ range (min (j : ℕ) k), (t - x l) := by
  induction k generalizing j with
  | zero => simp [lowerFactorTPartial]
  | succ k ih =>
    rw [lowerFactorTPartial_succ, ← vecMul_vecMul, vecMul_transpose_lowerBidiag_apply]
    split_ifs with h
    · rw [ih (by omega), ih (by omega)]
      simp only
      rw [min_eq_right (by omega : k ≤ (j : ℕ)), min_eq_right (by omega : k ≤ (j : ℕ) - 1),
        min_eq_right (by omega : k + 1 ≤ (j : ℕ)), prod_range_succ]
      obtain ⟨d, hd⟩ : ∃ d, (j : ℕ) - k = d + 1 := ⟨(j : ℕ) - k - 1, by omega⟩
      rw [hd, show (j : ℕ) - 1 - k = d by omega, show (j : ℕ) - (k + 1) = d by omega, pow_succ]
      ring
    · rw [ih (by omega), min_eq_left (by omega : (j : ℕ) ≤ k),
        min_eq_left (by omega : (j : ℕ) ≤ k + 1)]

/-- The Newton-to-monomial sweep in row form. Let $R$ be a commutative ring, let
$x_0, \dots, x_n \in R$, and let $t \in R$. Then the row of powers $(1, t, \dots, t^n)$ times
$L^T$ is the row of Newton basis values: $$\bigl((1, t, \dots, t^n) \, L^T\bigr)_j = \prod_{l <
j} (t - x_l), \qquad 0 \le j \le n.$$ This is (4.6.4) of [golub2013matrix]. -/
theorem pow_vecMul_lowerFactorT (x : Fin (n + 1) → R) (t : R) (j : Fin (n + 1)) :
    ((fun j : Fin (n + 1) => t ^ (j : ℕ)) ᵥ* lowerFactorT x) j =
      ∏ l ∈ range j, (t - x l) := by
  have := pow_vecMul_lowerFactorTPartial x t le_rfl j
  rw [min_eq_left (by omega : (j : ℕ) ≤ n), Nat.sub_self, pow_zero, one_mul] at this
  exact this

/-- The product $V^T L^T$ is the Newton basis matrix. For nodes $x_0, \dots, x_n$ in a commutative
ring, $$(V^T L^T)_{ij} = \prod_{l < j} (x_i - x_l).$$ This is §4.6.2 of [golub2013matrix].

The matrix $V^T$ is `Matrix.vandermonde x`. The identity is
`BjorckPereyra.pow_vecMul_lowerFactorT` at $t = x_i$. -/
theorem vandermonde_mul_lowerFactorT (x : Fin (n + 1) → R) :
    vandermonde x * lowerFactorT x = of fun i (j : Fin (n + 1)) => ∏ l ∈ range j, (x i - x l) := by
  ext i j
  rw [of_apply, ← pow_vecMul_lowerFactorT x (x i) j]
  rfl

/-- The Newton-to-monomial sweep is $a = L^T c$. Let $R$ be a commutative ring, let
$x_0, \dots, x_n \in R$, and let $c \in R^{n+1}$. Then the polynomial with coefficients $L^T c$
is the Newton form with coefficients $c$: $$\sum_{j=0}^n (L^T c)_j X^j = \sum_{k=0}^n c_k
\prod_{i < k} (X - x_i).$$ This is (4.6.4) of [golub2013matrix], with the recursion
$p_k = c_k + (x - x_k) p_{k+1}$ that precedes it. -/
theorem lowerFactorT_mulVec_newtonCoeff (x : Fin (n + 1) → R) (c : Fin (n + 1) → R) :
    ∑ j, C ((lowerFactorT x *ᵥ c) j) * X ^ (j : ℕ) =
      ∑ k : Fin (n + 1), C (c k) * ∏ i ∈ range k, (X - C (x i)) := by
  have hmap : (lowerFactorT x).map C = lowerFactorT (fun i => C (x i)) := by
    have : ∀ k : ℕ, (lowerBidiag n k (x k))ᵀ.map C = (lowerBidiag n k (C (x k)))ᵀ := by
      intro k
      ext i j
      simp only [map_apply, transpose_apply, lowerBidiag, of_apply]
      split_ifs <;> simp
    rw [lowerFactorT, lowerFactorT, ← RingHom.mapMatrix_apply, map_list_prod, List.map_map]
    congr 1
    refine List.map_congr_left fun k _ => ?_
    simp only [Function.comp_apply, RingHom.mapMatrix_apply, this]
  have key := fun k => pow_vecMul_lowerFactorT (fun i => C (x i)) (X : R[X]) k
  rw [← hmap] at key
  calc ∑ j, C ((lowerFactorT x *ᵥ c) j) * X ^ (j : ℕ)
      = ∑ j : Fin (n + 1), ∑ k : Fin (n + 1), X ^ (j : ℕ) * C (lowerFactorT x j k) * C (c k) := by
        refine sum_congr rfl fun j _ => ?_
        simp only [mulVec, dotProduct, map_sum, map_mul, sum_mul]
        exact sum_congr rfl fun k _ => by ring
    _ = ∑ k, C (c k) * ((fun j : Fin (n + 1) => (X : R[X]) ^ (j : ℕ)) ᵥ*
          (lowerFactorT x).map C) k := by
        rw [sum_comm]
        refine sum_congr rfl fun k _ => ?_
        simp only [vecMul, dotProduct, map_apply, mul_sum]
        exact sum_congr rfl fun j _ => by ring
    _ = _ := by simp only [key]

/-- The nodes as a family indexed by $\mathbb{N}$: an index is cast into `Fin (n + 1)` modulo
$n + 1$, and the values past $n$ are never read. -/
private def nodeN (x : Fin (n + 1) → R) (i : ℕ) : R := x i

omit [CommRing R] in
private theorem nodeN_injOn {x : Fin (n + 1) → R} (hx : Function.Injective x) :
    Set.InjOn (nodeN x) (Set.Iic n) := by
  intro i hi j hj h
  have := hx h
  simp only [Set.mem_Iic] at hi hj
  have := congrArg Fin.val this
  simp only [Fin.val_natCast, Nat.mod_eq_of_lt (Nat.lt_succ_of_le hi),
    Nat.mod_eq_of_lt (Nat.lt_succ_of_le hj)] at this
  exact this

omit [CommRing R] in
private theorem nodeN_val (x : Fin (n + 1) → R) (i : Fin (n + 1)) : nodeN x i = x i := by
  simp [nodeN]

end Ring

section Field

variable {K : Type*} [Field K] {n : ℕ}

/-- The diagonal factor $D_k$ of [golub2013matrix] §4.6.2. For nodes $x_0, \dots, x_n$ in a field
and $k \in \mathbb{N}$, $$D_k = \operatorname{diag}(1, \dots, 1, x_{k+1} - x_0, \dots, x_n -
x_{n-k-1}),$$ with $k + 1$ ones: entry $i$ is $1$ for $i \le k$ and $x_i - x_{i-k-1}$ for
$i > k$. For $k \ge n$, $D_k$ is the identity matrix. -/
def diffScale (x : Fin (n + 1) → K) (k : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  diagonal fun i => if (i : ℕ) ≤ k then 1 else x i - x ⟨i - k - 1, by omega⟩

/-- The factor $U^T$ of the divided-difference sweep of [golub2013matrix] §4.6.2. For nodes
$x_0, \dots, x_n$ in a field, $$U^T = D_{n-1}^{-1} L_{n-1}(1) \cdots D_0^{-1} L_0(1).$$ Its
transpose is the upper triangular matrix $U$ of the book.

The inverse is Mathlib's matrix inverse, which is $0$ for a singular matrix. For distinct nodes
each $D_k$ is invertible (`BjorckPereyra.inv_diffScale`). -/
noncomputable def upperFactorT (x : Fin (n + 1) → K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  ((List.range n).map fun k => (diffScale x k)⁻¹ * lowerBidiag n k 1).reverse.prod

/-- For distinct nodes, $D_k^{-1}$ is the diagonal matrix of the reciprocals of the diagonal entries
of $D_k$. -/
theorem inv_diffScale {x : Fin (n + 1) → K} (hx : Function.Injective x) (k : ℕ) :
    (diffScale x k)⁻¹ =
      diagonal fun i : Fin (n + 1) =>
        (if (i : ℕ) ≤ k then 1 else x i - x ⟨i - k - 1, by omega⟩)⁻¹ := by
  refine inv_eq_left_inv ?_
  rw [diffScale, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  refine inv_mul_cancel₀ ?_
  split_ifs with h
  · exact one_ne_zero
  · exact sub_ne_zero.mpr fun h' => by have := congrArg Fin.val (hx h'); simp at this; omega

/-- The partial product $D_{k-1}^{-1} L_{k-1}(1) \cdots D_0^{-1} L_0(1)$. -/
private noncomputable def upperFactorTPartial (x : Fin (n + 1) → K) (k : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  ((List.range k).map fun k => (diffScale x k)⁻¹ * lowerBidiag n k 1).reverse.prod

private theorem upperFactorTPartial_succ (x : Fin (n + 1) → K) (k : ℕ) :
    upperFactorTPartial x (k + 1) =
      (diffScale x k)⁻¹ * lowerBidiag n k 1 * upperFactorTPartial x k := by
  simp [upperFactorTPartial, List.range_succ]

/-- The invariant of the divided-difference sweep: for distinct nodes and $k \le n$, entry $i$ of
the vector $(g(x_j))_j$ after $k$ factors is the divided difference of $g$ over the nodes $x_l$
with $\max(i - k, 0) \le l \le i$. -/
private theorem upperFactorTPartial_mulVec {x : Fin (n + 1) → K} (hx : Function.Injective x)
    (g : K → K) {k : ℕ} (hk : k ≤ n) (i : Fin (n + 1)) :
    (upperFactorTPartial x k *ᵥ fun j => g (x j)) i =
      DividedDifference.newtonOn (Icc ((i : ℕ) - k) i) (nodeN x) g := by
  induction k generalizing i with
  | zero => simp [upperFactorTPartial, nodeN_val]
  | succ k ih =>
    rw [upperFactorTPartial_succ, ← mulVec_mulVec, ← mulVec_mulVec, inv_diffScale hx,
      mulVec_diagonal, lowerBidiag_mulVec_apply]
    split_ifs with h h'
    · exfalso; omega
    · rw [ih (by omega), inv_one, one_mul]
      congr 1
      ext l
      simp only [mem_Icc]
      omega
    · rw [ih (by omega), ih (by omega)]
      simp only [one_mul]
      have hwin : Set.InjOn (nodeN x) (Icc ((i : ℕ) - (k + 1)) i : Finset ℕ) := by
        refine (nodeN_injOn hx).mono fun l hl => ?_
        simp only [coe_Icc, Set.mem_Icc] at hl
        simp only [Set.mem_Iic]
        omega
      rw [DividedDifference.newtonOn_eq_sub_div hwin g (i := (i : ℕ)) (j := (i : ℕ) - (k + 1))
        (by simp) (by simp) (by omega)]
      have e1 : (Icc ((i : ℕ) - (k + 1)) i).erase ((i : ℕ) - (k + 1)) = Icc ((i : ℕ) - k) i := by
        ext l; simp only [mem_erase, mem_Icc]; omega
      have e2 : (Icc ((i : ℕ) - (k + 1)) i).erase (i : ℕ) = Icc ((i : ℕ) - 1 - k) (i - 1) := by
        ext l; simp only [mem_erase, mem_Icc]; omega
      rw [e1, e2, div_eq_inv_mul]
      congr 1
      rw [nodeN_val]
      congr 2
      rw [nodeN]
      congr 1
      ext
      rw [Fin.val_natCast, Nat.mod_eq_of_lt (by omega)]
      change (i : ℕ) - k - 1 = _
      omega
    · exfalso; omega

/-- The divided-difference sweep is $c = U^T f$. Let $K$ be a field, let $x_0, \dots, x_n \in K$ be
distinct, and let $g : K \to K$ and $f_i = g(x_i)$. Then for $0 \le k \le n$, $$(U^T f)_k =
g[x_0, \dots, x_k],$$ the divided difference of $g$ at the nodes $x_0, \dots, x_k$. This is
§4.6.2 of [golub2013matrix], where the book says that "it is easy to verify from (4.6.3)".

The divided difference is `DividedDifference.newtonOn (Finset.Iic k) x g`, which is $\sum_{i \le
k} g(x_i) / \prod_{j \le k, \, j \ne i} (x_i - x_j)$. -/
theorem upperFactorT_mulVec_eq_newtonOn {x : Fin (n + 1) → K} (hx : Function.Injective x)
    (g : K → K) (k : Fin (n + 1)) :
    (upperFactorT x *ᵥ fun j => g (x j)) k = DividedDifference.newtonOn (Iic k) x g := by
  have := upperFactorTPartial_mulVec hx g le_rfl k
  rw [show (k : ℕ) - n = 0 by omega] at this
  refine this.trans ?_
  have hmap : (Iic k).map Fin.valEmbedding = Icc 0 (k : ℕ) := by
    rw [Fin.map_valEmbedding_Iic]
    ext l
    simp
  rw [← hmap, DividedDifference.newtonOn_map]
  congr 1
  funext l
  exact nodeN_val x l

/-- The **Björck–Pereyra factorization**. For distinct nodes $x_0, \dots, x_n$ in a field,
$$V^{-T} = L^T U^T.$$ This is §4.6.2 of [golub2013matrix].

The Lean statement is `(vandermonde x)⁻¹ = lowerFactorT x * upperFactorT x`, because Mathlib's
`Matrix.vandermonde x` is the matrix $V^T$ of the book. Its transpose $V^{-1} = UL$ is the form
that Algorithm 4.6.2 applies. -/
theorem inv_vandermonde_eq {x : Fin (n + 1) → K} (hx : Function.Injective x) :
    (vandermonde x)⁻¹ = lowerFactorT x * upperFactorT x := by
  refine inv_eq_right_inv ?_
  rw [← Matrix.mul_assoc, vandermonde_mul_lowerFactorT]
  ext i j
  -- the `j`-th column of `Uᵀ` is `Uᵀ` applied to the `j`-th unit vector
  set f : Fin (n + 1) → K := Pi.single j 1
  set g : K → K := Function.extend x f 0
  have hg : (fun l => g (x l)) = f := funext fun l => hx.extend_apply f 0 l
  have hcol : ∀ l, upperFactorT x l j = (upperFactorT x *ᵥ fun l => g (x l)) l := by
    intro l
    rw [hg, mulVec_single_one]
    rfl
  simp only [Matrix.mul_apply, of_apply, hcol, upperFactorT_mulVec_eq_newtonOn hx]
  -- Newton's formula evaluated at the node `x i`
  have hN := DividedDifference.interpolate_eq_sum_newtonOn_mul_nodal
    (s := (univ : Finset (Fin (n + 1)))) (hx.injOn) g
  have hv := congrArg (eval (x i)) hN
  rw [Lagrange.eval_interpolate_at_node _ hx.injOn (mem_univ i), eval_finsetSum] at hv
  simp only [eval_mul, eval_C, Lagrange.eval_nodal] at hv
  have h1 : g (x i) = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K) i j := by
    rw [congrFun hg i, Matrix.one_apply]
    simp [f, Pi.single_apply]
  rw [← h1, hv]
  refine sum_congr rfl fun l _ => ?_
  have hle : univ.filter (· ≤ l) = Iic l := by ext; simp
  have hlt : ∏ m ∈ univ.filter (· < l), (x i - x m) = ∏ m ∈ range l, (x i - x m) := by
    have hmap : (univ.filter (· < l)).map Fin.valEmbedding = range l := by
      ext m
      simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_range]
      constructor
      · rintro ⟨a, ha, rfl⟩; exact ha
      · intro hm; exact ⟨⟨m, by omega⟩, hm, rfl⟩
    rw [← hmap, prod_map]
    refine prod_congr rfl fun m _ => ?_
    simp
  rw [hle, hlt, mul_comm]

end Field

end BjorckPereyra
