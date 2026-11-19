/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Direct.Vandermonde
import NumlibSurface.GolubVanLoan.Chapter01.Section04

/-!
# Golub and Van Loan, Section 4.6: Vandermonde systems

This module formalizes §4.6 of [golub2013matrix], linear systems with the Vandermonde matrix $V =
V(x_0, \dots, x_n) \in \mathbb{R}^{(n+1) \times (n+1)}$, whose entry $(i, j)$ is $x_j^i$. The system
$V^T a = f$ is polynomial interpolation: it holds if and only if $p(x) = \sum_j a_j x^j$ satisfies
$p(x_i) = f_i$ for all $i$ (4.6.1), so $V$ is nonsingular exactly when the nodes $x_i$ are distinct.
The interpolant has the Newton form $p(x) = \sum_k c_k \prod_{i < k} (x - x_i)$ with the divided
differences $c_k = f[x_0, \dots, x_k]$ (4.6.2). The Björck–Pereyra algorithms compute the divided
differences by a product $U^T$ of elementary matrices and then the monomial coefficients by a
product $L^T$, so that $V^{-T} = L^T U^T$ (§4.6.2). Algorithm 4.6.1 solves $V^T a = f$ and Algorithm
4.6.2 solves $Vz = b$ in this way.

The proofs specialize the backbone modules `Numlib.Direct.Vandermonde` and
`Numlib.Approximation.NewtonForm`, and Mathlib's `Matrix.vandermonde`,
`Matrix.det_vandermonde_ne_zero_iff` and `Lagrange.interpolate`. The remark that the discrete
Fourier transform matrix is a Vandermonde matrix uses `GolubVanLoan.Chapter01.fourierMatrix` of
§1.4.

## Main definitions

* §4.6, `GolubVanLoan.Chapter04.vandermondeCols`: the Vandermonde matrix $V(x_0, \dots, x_n)$, with
  entries $x_j^i$.
* Algorithm 4.6.1, `GolubVanLoan.Chapter04.algorithm_4_6_1`: the Björck–Pereyra algorithm for
  $V^T a = f$.
* Algorithm 4.6.2, `GolubVanLoan.Chapter04.algorithm_4_6_2`: the Björck–Pereyra algorithm for
  $Vz = b$.

## Main results

* §4.6, `GolubVanLoan.Chapter04.dft_eq_vandermonde`: the DFT matrix $F_n$ is the Vandermonde matrix
  of the nodes $\omega_n^k$.
* (4.6.1), `GolubVanLoan.Chapter04.equation_4_6_1`: $V^T a = f$ if and only if
  $p(x) = \sum_j a_j x^j$ interpolates the data $f$ at the nodes.
* §4.6.1, `GolubVanLoan.Chapter04.vandermonde_isUnit_iff`: $V$ is nonsingular if and only if the
  nodes are distinct.
* (4.6.2), `GolubVanLoan.Chapter04.equation_4_6_2`: for distinct nodes, the Newton coefficients of
  the interpolant are the divided differences.
* §4.6.2, `GolubVanLoan.Chapter04.vandermonde_inv_factorization`: $U^T$ maps data to divided
  differences, $L^T$ maps Newton coefficients to monomial coefficients, and $V^{-T} = L^T U^T$.
* Algorithm 4.6.1, `GolubVanLoan.Chapter04.algorithm_4_6_1_spec`: for distinct nodes, the exact run
  solves $V^T a = f$.
* Algorithm 4.6.2, `GolubVanLoan.Chapter04.algorithm_4_6_2_spec`: for distinct nodes, the exact run
  solves $Vz = b$.

## Conventions

* The source indexes from $0$ in this section, and so does this module: the nodes are
  `x : Fin (n + 1) → ℝ`, and "the $x_i$ are distinct" is `Function.Injective x`.
* The source's $V(x_0, \dots, x_n)$, whose columns are the powers of the nodes, is
  `GolubVanLoan.Chapter04.vandermondeCols x`, the transpose of Mathlib's `Matrix.vandermonde x`,
  whose rows are the powers of the nodes.
* The elementary lower bidiagonal matrix $L_k(\alpha)$ of §4.6.2 is the identity with $-\alpha$ at
  the positions $(i + 1, i)$ for $i \ge k$; it is `BjorckPereyra.lowerBidiag n k α`. The diagonal
  matrix $D_k = \operatorname{diag}(1, \dots, 1, x_{k+1} - x_0, \dots, x_n - x_{n-k-1})$, with
  $k + 1$ ones, is `BjorckPereyra.diffScale x k`.
* The factors $U^T = D_{n-1}^{-1} L_{n-1}(1) \cdots D_0^{-1} L_0(1)$ and
  $L^T = L_0(x_0)^T \cdots L_{n-1}(x_{n-1})^T$ are `BjorckPereyra.upperFactorT x` and
  `BjorckPereyra.lowerFactorT x`.

## Implementation notes

* The algorithms follow the algorithm conventions of the library index: every difference, product
  and quotient passes through the rounding hook `rnd`, the differences of nodes included.
* The inner loops run over the index lists of the source. The loop $i = n{:}{-1}{:}k{+}1$ runs
  over the indices $i \ge k$ in `Fin n` in decreasing order and acts on the entry `i.succ`, so
  that the source's $i - 1$ is `i.castSucc`. The loop $i = k{:}n{-}1$ runs over the same indices
  in increasing order and acts on the entry `i.castSucc`, so that the source's $i + 1$ is
  `i.succ`.
* These loop orders make every step read only values that the same pass has not yet overwritten. The
  exact runs are therefore the products of the factors of §4.6.2.

## Deviations from the source

* **Generalization.** The nonsingularity criterion includes the converse. See
  `GolubVanLoan.Chapter04.vandermonde_isUnit_iff`.
* **Correction.** The Newton interpolant can have degree less than $n$. See
  `GolubVanLoan.Chapter04.equation_4_6_2`.
* **Reading.** The Björck–Pereyra programs totalize division and use a rounding hook. See
  `GolubVanLoan.Chapter04.algorithm_4_6_1`, `GolubVanLoan.Chapter04.algorithm_4_6_2`.

## Not formalized

* **Displays (4.6.3)–(4.6.4)** as separate results. They are the two stages of Algorithm 4.6.1,
  which `GolubVanLoan.Chapter04.vandermonde_inv_factorization` and
  `GolubVanLoan.Chapter04.algorithm_4_6_1_spec` cover.
* **The accuracy remark of Björck and Pereyra.**
* **Confluent Vandermonde systems.**
-/

open Matrix hiding vandermonde
open Polynomial Finset
open scoped Fin.NatCast

namespace GolubVanLoan.Chapter04

variable {n : ℕ}

/-! ### §4.6 The Vandermonde matrix -/

/-- **Section 4.6** of [golub2013matrix], the Vandermonde matrix. Let
$x_0, \dots, x_n \in \mathbb{R}$. The **Vandermonde matrix** $V = V(x_0, \dots, x_n) \in
\mathbb{R}^{(n+1) \times (n+1)}$ is
$$V = \begin{bmatrix} 1 & 1 & \cdots & 1 \\ x_0 & x_1 & \cdots & x_n \\ \vdots & \vdots & &
  \vdots \\ x_0^n & x_1^n & \cdots & x_n^n \end{bmatrix},$$
that is, its entry $(i, j)$ is $x_j^i$ for $i, j = 0, \dots, n$.

It is the transpose of Mathlib's `Matrix.vandermonde x`, whose entry $(i, j)$ is $x_i^j$. -/
def vandermondeCols (x : Fin (n + 1) → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  (Matrix.vandermonde x)ᵀ

/-- The entries of the Vandermonde matrix: $V(x_0, \dots, x_n)_{ij} = x_j^i$. -/
theorem vandermondeCols_apply (x : Fin (n + 1) → ℝ) (i j : Fin (n + 1)) :
    vandermondeCols x i j = x j ^ (i : ℕ) := rfl

/-- **Section 4.6** of [golub2013matrix], the DFT matrix as a Vandermonde matrix. Let
$n \in \mathbb{N}$ and $\omega_n = \exp(-2\pi i/n)$. The DFT matrix $F_n = (\omega_n^{kj})$ of
§1.4.1 is the Vandermonde matrix of the nodes $1, \omega_n, \dots, \omega_n^{n-1}$:
$$(F_n)_{kj} = (\omega_n^k)^j, \qquad k, j = 0, \dots, n-1.$$

The source calls $F_n$ a very special complex Vandermonde matrix. The theorem uses Mathlib's
`Matrix.vandermonde`, whose rows are the powers of the nodes; since $F_n$ is symmetric, it is
also the transpose, the source's $V(1, \omega_n, \dots, \omega_n^{n-1})$. The matrix $F_n$ is
`GolubVanLoan.Chapter01.fourierMatrix n`. -/
theorem dft_eq_vandermonde (n : ℕ) :
    Chapter01.fourierMatrix n =
      Matrix.vandermonde fun k : Fin n => Complex.exp (-2 * Real.pi * Complex.I / n) ^ (k : ℕ) := by
  ext k j
  rw [Chapter01.fourierMatrix_apply, Matrix.vandermonde_apply, ← pow_mul]

/-! ### §4.6.1 Polynomial interpolation: $V^T a = f$ -/

/-- **Equation (4.6.1)** of [golub2013matrix]. Let $x, a, f \in \mathbb{R}^{n+1}$, and let
$p(x) = \sum_{j=0}^{n} a_j x^j$. Then
$$V(x_0, \dots, x_n)^T a = f \iff p(x_i) = f_i \text{ for } i = 0, \dots, n.$$

The source states that solving $V^T a = f$ is equivalent to polynomial interpolation. The nodes
need not be distinct. -/
theorem equation_4_6_1 (x a f : Fin (n + 1) → ℝ) :
    (vandermondeCols x)ᵀ *ᵥ a = f ↔ ∀ i, (∑ j, C (a j) * X ^ (j : ℕ)).eval (x i) = f i := by
  rw [vandermondeCols, transpose_transpose, funext_iff]
  simp only [Matrix.vandermonde_mulVec_eq_eval]

/-- **Section 4.6.1** of [golub2013matrix], nonsingularity of $V$. Let
$x_0, \dots, x_n \in \mathbb{R}$. The Vandermonde matrix $V(x_0, \dots, x_n)$ is nonsingular if
and only if the $x_i$ are distinct.

The source states the "if" direction, as a consequence of (4.6.1).

**Generalization.** Lean proves both directions of the criterion. The text uses distinctness to
obtain nonsingularity.
-/
theorem vandermonde_isUnit_iff (x : Fin (n + 1) → ℝ) :
    IsUnit (vandermondeCols x) ↔ Function.Injective x := by
  rw [isUnit_iff_isUnit_det, vandermondeCols, det_transpose, isUnit_iff_ne_zero,
    Matrix.det_vandermonde_ne_zero_iff]

/-- **Equation (4.6.2)** of [golub2013matrix], the Newton form of the interpolant. Let
$x_0, \dots, x_n \in \mathbb{R}$ be distinct, and let $g : \mathbb{R} \to \mathbb{R}$. The
polynomial $p$ of degree at most $n$ with $p(x_i) = g(x_i)$ for $i = 0, \dots, n$ is
$$p(x) = \sum_{k=0}^{n} c_k \prod_{i=0}^{k-1} (x - x_i),$$
where the constants $c_k = g[x_0, \dots, x_k]$ are the divided differences
$$g[x_0, \dots, x_k] = \sum_{i=0}^{k} \frac{g(x_i)}{\prod_{j \le k, j \neq i} (x_i - x_j)}.$$

The source computes this Newton representation as the first step of solving (4.6.1). The
interpolant is `Lagrange.interpolate`, and the divided difference is
`DividedDifference.newtonOn` over the index set $\{0, \dots, k\}$.

**Correction.** The interpolant has degree at most $n$. The text describes it as having degree $n$,
but the highest coefficient may vanish, for example for constant data when $n > 0$.
-/
theorem equation_4_6_2 {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) (g : ℝ → ℝ) :
    Lagrange.interpolate univ x (fun i => g (x i)) =
      ∑ k, C (DividedDifference.newtonOn (Iic k) x g) * ∏ i ∈ Iio k, (X - C (x i)) := by
  rw [DividedDifference.interpolate_eq_sum_newtonOn_mul_nodal (s := univ) hx.injOn g]
  refine sum_congr rfl fun k _ => ?_
  have hle : ({i ∈ univ | i ≤ k} : Finset (Fin (n + 1))) = Iic k := by ext; simp
  have hlt : ({i ∈ univ | i < k} : Finset (Fin (n + 1))) = Iio k := by ext; simp
  rw [hle, hlt, Lagrange.nodal]

/-! ### §4.6.2 The factorization $V^{-T} = L^T U^T$ -/

/-- **Section 4.6.2** of [golub2013matrix], the factorization $V^{-T} = L^T U^T$. Let
$x_0, \dots, x_n \in \mathbb{R}$ be distinct, let $V = V(x_0, \dots, x_n)$, and let
$$U^T = D_{n-1}^{-1} L_{n-1}(1) \cdots D_0^{-1} L_0(1), \qquad L^T = L_0(x_0)^T \cdots
  L_{n-1}(x_{n-1})^T,$$
where $L_k(\alpha)$ is the identity with $-\alpha$ at the positions $(i + 1, i)$ for $i \ge k$,
and $D_k = \operatorname{diag}(1, \dots, 1, x_{k+1} - x_0, \dots, x_n - x_{n-k-1})$ with $k + 1$
ones. Then:

1. For every $g : \mathbb{R} \to \mathbb{R}$, the vector $c = U^T f$ with $f_j = g(x_j)$ is the
   vector of divided differences, $c_k = g[x_0, \dots, x_k]$.
2. For every $c \in \mathbb{R}^{n+1}$, the vector $a = L^T c$ is the vector of monomial
   coefficients of the Newton form: $\sum_j a_j x^j = \sum_k c_k \prod_{i < k} (x - x_i)$ as
   polynomials.
3. $V^{-T} = L^T U^T$.
4. $V^{-1} = UL$.

The source verifies the first two parts from the stages (4.6.3) and (4.6.4) of Algorithm 4.6.1,
and concludes that the algorithm solves $V^T a = f$ by tacitly computing the "UL factorization"
of $V^{-1}$. The factors are `BjorckPereyra.upperFactorT` and `BjorckPereyra.lowerFactorT`, and
the divided difference is `DividedDifference.newtonOn`. -/
theorem vandermonde_inv_factorization {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) :
    (∀ (g : ℝ → ℝ) (k : Fin (n + 1)), (BjorckPereyra.upperFactorT x *ᵥ fun j => g (x j)) k =
      DividedDifference.newtonOn (Iic k) x g) ∧
    (∀ c : Fin (n + 1) → ℝ, ∑ j, C ((BjorckPereyra.lowerFactorT x *ᵥ c) j) * X ^ (j : ℕ) =
      ∑ k : Fin (n + 1), C (c k) * ∏ i ∈ range k, (X - C (x i))) ∧
    (vandermondeCols x)⁻¹ᵀ = BjorckPereyra.lowerFactorT x * BjorckPereyra.upperFactorT x ∧
    (vandermondeCols x)⁻¹ = (BjorckPereyra.upperFactorT x)ᵀ * (BjorckPereyra.lowerFactorT x)ᵀ := by
  refine ⟨fun g k => BjorckPereyra.upperFactorT_mulVec_eq_newtonOn hx g k,
    fun c => BjorckPereyra.lowerFactorT_mulVec_newtonCoeff x c, ?_, ?_⟩
  · rw [vandermondeCols, ← transpose_nonsing_inv, transpose_transpose,
      BjorckPereyra.inv_vandermonde_eq hx]
  · rw [vandermondeCols, ← transpose_nonsing_inv, BjorckPereyra.inv_vandermonde_eq hx,
      transpose_mul]

/-! ### Algorithms 4.6.1 and 4.6.2 -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 4.6.1** of [golub2013matrix]. Given $x(0{:}n) \in \mathbb{R}^{n+1}$ with distinct
entries and $f = f(0{:}n) \in \mathbb{R}^{n+1}$, the algorithm overwrites $f$ with the solution
$a = a(0{:}n)$ of the Vandermonde system $V(x_0, \dots, x_n)^T a = f$:
```
for k = 0:n−1
    for i = n:−1:k+1
        f(i) = (f(i) − f(i−1)) / (x(i) − x(i−k−1))
    end
end
for k = n−1:−1:0
    for i = k:n−1
        f(i) = f(i) − f(i+1) · x(k)
    end
end
```
The program computes $f_i \leftarrow \mathrm{fl}(\mathrm{fl}(f_i - f_{i-1}) / \mathrm{fl}(x_i -
x_{i-k-1}))$ in the first sweep and $f_i \leftarrow \mathrm{fl}(f_i - \mathrm{fl}(f_{i+1} x_k))$
in the second. The differences of nodes are computed, hence rounded.

**Reading.** The program preserves the loop orders and rounds each arithmetic operation, including
the node differences. Its type accepts repeated nodes using totalized division. The exact solve
theorem assumes distinct nodes as in the source.
-/
noncomputable def algorithm_4_6_1 (x f : Fin (n + 1) → ℝ) : M (Fin (n + 1) → ℝ) := do
  let c ← (List.finRange n).foldlM (fun (f : Fin (n + 1) → ℝ) (k : Fin n) =>
    ((List.finRange n).filter (fun i : Fin n => k ≤ i)).reverse.foldlM
      (fun (f : Fin (n + 1) → ℝ) (i : Fin n) => do
        let num ← rnd (f i.succ - f i.castSucc)
        let den ← rnd (x i.succ - x ⟨(i : ℕ) - (k : ℕ), by have := i.isLt; omega⟩)
        let q ← rnd (num / den)
        pure (Function.update f i.succ q)) f) f
  (List.finRange n).reverse.foldlM (fun (a : Fin (n + 1) → ℝ) (k : Fin n) =>
    ((List.finRange n).filter (fun i : Fin n => k ≤ i)).foldlM
      (fun (a : Fin (n + 1) → ℝ) (i : Fin n) => do
        let p ← rnd (a i.succ * x k.castSucc)
        let r ← rnd (a i.castSucc - p)
        pure (Function.update a i.castSucc r)) a) c

/-- **Algorithm 4.6.2** of [golub2013matrix]. Given $x(0{:}n) \in \mathbb{R}^{n+1}$ with distinct
entries and $b = b(0{:}n) \in \mathbb{R}^{n+1}$, the algorithm overwrites $b$ with the solution
$z = z(0{:}n)$ of the Vandermonde system $V(x_0, \dots, x_n) z = b$:
```
for k = 0:n−1
    for i = n:−1:k+1
        b(i) = b(i) − x(k) b(i−1)
    end
end
for k = n−1:−1:0
    for i = k+1:n
        b(i) = b(i) / (x(i) − x(i−k−1))
    end
    for i = k:n−1
        b(i) = b(i) − b(i+1)
    end
end
```
The program computes $b_i \leftarrow \mathrm{fl}(b_i - \mathrm{fl}(x_k b_{i-1}))$ in the first
sweep, and $b_i \leftarrow \mathrm{fl}(b_i / \mathrm{fl}(x_i - x_{i-k-1}))$ and then
$b_i \leftarrow \mathrm{fl}(b_i - b_{i+1})$ in the second.

**Reading.** The program preserves the loop orders and rounds each arithmetic operation, including
the node differences. Its type accepts repeated nodes using totalized division. The exact solve
theorem assumes distinct nodes as in the source.
-/
noncomputable def algorithm_4_6_2 (x b : Fin (n + 1) → ℝ) : M (Fin (n + 1) → ℝ) := do
  let y ← (List.finRange n).foldlM (fun (b : Fin (n + 1) → ℝ) (k : Fin n) =>
    ((List.finRange n).filter (fun i : Fin n => k ≤ i)).reverse.foldlM
      (fun (b : Fin (n + 1) → ℝ) (i : Fin n) => do
        let p ← rnd (x k.castSucc * b i.castSucc)
        let r ← rnd (b i.succ - p)
        pure (Function.update b i.succ r)) b) b
  (List.finRange n).reverse.foldlM (fun (b : Fin (n + 1) → ℝ) (k : Fin n) => do
    let b ← ((List.finRange n).filter (fun i : Fin n => k ≤ i)).foldlM
      (fun (b : Fin (n + 1) → ℝ) (i : Fin n) => do
        let d ← rnd (x i.succ - x ⟨(i : ℕ) - (k : ℕ), by have := i.isLt; omega⟩)
        let q ← rnd (b i.succ / d)
        pure (Function.update b i.succ q)) b
    ((List.finRange n).filter (fun i : Fin n => k ≤ i)).foldlM
      (fun (b : Fin (n + 1) → ℝ) (i : Fin n) => do
        let r ← rnd (b i.castSucc - b i.succ)
        pure (Function.update b i.castSucc r)) b) y

end Programs

/-! ### Exact semantics of the algorithms -/

/-- A loop of updates in which no step reads an entry that a step writes: each written entry ends
with the value computed from the initial state, and the other entries are unchanged. -/
private theorem foldl_update_eq {ι κ β : Type*} [DecidableEq κ] (w : ι → κ)
    (h : ι → (κ → β) → β) (l : List ι)
    (hl : l.Pairwise fun a b => w a ≠ w b ∧
      ∀ g g' : κ → β, (∀ t, t ≠ w a → g t = g' t) → h b g = h b g') (f : κ → β) :
    (∀ i ∈ l, l.foldl (fun g i => Function.update g (w i) (h i g)) f (w i) = h i f) ∧
      ∀ t, (∀ i ∈ l, w i ≠ t) →
        l.foldl (fun g i => Function.update g (w i) (h i g)) f t = f t :=
  ⟨fun _ hi => List.foldl_update_apply_of_pairwise w h hl f hi,
    fun _ ht => List.foldl_update_apply_of_forall_ne w h ht f⟩

/-- Applying the product $S_{k_r} \cdots S_{k_1}$ to $f$ is the loop that applies $S_{k_1}$, then
$S_{k_2}$, and so on. -/
private theorem reverse_prod_mulVec {α : Type*} (S : α → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (l : List α) (f : Fin (n + 1) → ℝ) :
    (l.map S).reverse.prod *ᵥ f = l.foldl (fun f k => S k *ᵥ f) f := by
  induction l generalizing f with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.reverse_cons, List.prod_append, List.prod_singleton, ← mulVec_mulVec,
      ih, List.foldl_cons]

/-- Applying the product $S_{k_1} \cdots S_{k_r}$ to $f$ is the loop that applies the factors in the
reversed order of the list. -/
private theorem prod_mulVec {α : Type*} (S : α → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (l : List α) (f : Fin (n + 1) → ℝ) :
    (l.map S).prod *ᵥ f = l.reverse.foldl (fun f k => S k *ᵥ f) f := by
  rw [← List.reverse_reverse (l.map S), ← List.map_reverse, reverse_prod_mulVec]

/-- A loop over `k : Fin n` is the loop over the natural numbers $k < n$. -/
private theorem foldl_finRange {β : Type*} (g : β → ℕ → β) (b : β) :
    (List.finRange n).foldl (fun b (k : Fin n) => g b k) b = (List.range n).foldl g b := by
  rw [← List.map_coe_finRange_eq_range, List.foldl_map]

/-- A loop over `k : Fin n` in decreasing order is the loop over the natural numbers $k < n$ in
decreasing order. -/
private theorem foldl_finRange_reverse {β : Type*} (g : β → ℕ → β) (b : β) :
    (List.finRange n).reverse.foldl (fun b (k : Fin n) => g b k) b =
      (List.range n).reverse.foldl g b := by
  rw [← List.map_coe_finRange_eq_range, ← List.map_reverse, List.foldl_map]

/-- The indices `i : Fin n` with $k \le i$, in increasing order, form a strictly increasing list. -/
private theorem pairwise_filter_le (k : Fin n) :
    ((List.finRange n).filter fun i : Fin n => k ≤ i).Pairwise (· < ·) :=
  (List.pairwise_lt_finRange n).filter _

private theorem mem_filter_le {k i : Fin n} :
    i ∈ (List.finRange n).filter (fun i : Fin n => k ≤ i) ↔ k ≤ i := by simp

/-- For distinct nodes, one pass of the first sweep of Algorithm 4.6.1 in exact arithmetic computes
$f \leftarrow D_k^{-1} L_k(1) f$. -/
private theorem sweep_divDiff {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) (k : Fin n)
    (f : Fin (n + 1) → ℝ) :
    ((List.finRange n).filter (fun i : Fin n => k ≤ i)).reverse.foldl
        (fun (f : Fin (n + 1) → ℝ) (i : Fin n) => Function.update f i.succ
          ((f i.succ - f i.castSucc) /
            (x i.succ - x ⟨(i : ℕ) - (k : ℕ), by have := i.isLt; omega⟩))) f =
      ((BjorckPereyra.diffScale x k)⁻¹ * BjorckPereyra.lowerBidiag n k 1) *ᵥ f := by
  obtain ⟨h1, h2⟩ := foldl_update_eq Fin.succ
    (fun (i : Fin n) (g : Fin (n + 1) → ℝ) => (g i.succ - g i.castSucc) /
      (x i.succ - x ⟨(i : ℕ) - (k : ℕ), by have := i.isLt; omega⟩))
    ((List.finRange n).filter (fun i : Fin n => k ≤ i)).reverse
    (List.pairwise_reverse.2 ((pairwise_filter_le k).imp fun {a b} hab => by
      refine ⟨fun h => (ne_of_lt hab) (Fin.succ_injective _ h).symm, fun g g' hg => ?_⟩
      have e1 : a.succ ≠ b.succ := fun h => (ne_of_lt hab) (Fin.succ_injective _ h)
      have e2 : a.castSucc ≠ b.succ := fun h => by
        have := congrArg Fin.val h
        simp only [Fin.val_castSucc, Fin.val_succ] at this
        have := Fin.lt_def.1 hab
        omega
      simp only [hg _ e1, hg _ e2])) f
  ext j
  rw [← mulVec_mulVec, BjorckPereyra.inv_diffScale hx, mulVec_diagonal,
    BjorckPereyra.lowerBidiag_mulVec_apply]
  by_cases hj : (k : ℕ) + 1 ≤ (j : ℕ)
  · have hj0 : (j : ℕ) - 1 < n := by have := j.isLt; omega
    set i : Fin n := ⟨(j : ℕ) - 1, hj0⟩
    have e1 : i.succ = j := Fin.ext (by simp [i]; omega)
    have hi : i ∈ ((List.finRange n).filter (fun i : Fin n => k ≤ i)).reverse := by
      rw [List.mem_reverse, mem_filter_le, Fin.le_def]
      simp [i]
      omega
    conv_lhs => rw [← e1]
    rw [h1 i hi, dite_eq_left hj, ite_eq_right (by omega), one_mul, div_eq_inv_mul]
    have e2 : i.castSucc = ⟨(j : ℕ) - 1, by omega⟩ := Fin.ext (by simp [i])
    have e3 : (⟨(i : ℕ) - (k : ℕ), by have := i.isLt; omega⟩ : Fin (n + 1)) =
        ⟨(j : ℕ) - k - 1, by omega⟩ := Fin.ext (by simp [i]; omega)
    rw [e1, e2, e3]
  · rw [h2 j fun i hi h => hj (by
      rw [List.mem_reverse, mem_filter_le, Fin.le_def] at hi
      rw [← h, Fin.val_succ]
      omega), dite_eq_right hj, ite_eq_left (by omega), inv_one, one_mul]

/-- For $i < n$, the entry $i$ of $L_k(\alpha)^T a$ is $a_i - \alpha a_{i+1}$ if $k \le i$, and
$a_i$ otherwise. -/
private theorem transpose_lowerBidiag_mulVec_castSucc (k : ℕ) (α : ℝ) (a : Fin (n + 1) → ℝ)
    (i : Fin n) :
    ((BjorckPereyra.lowerBidiag n k α)ᵀ *ᵥ a) i.castSucc =
      if k ≤ (i : ℕ) then a i.castSucc - a i.succ * α else a i.castSucc := by
  have hne : i.succ ≠ i.castSucc := fun h => by
    have := congrArg Fin.val h
    simp at this
  simp only [mulVec, dotProduct, transpose_apply, BjorckPereyra.lowerBidiag, of_apply]
  rw [Finset.sum_eq_add i.castSucc i.succ hne.symm (fun t _ ht => ?_) (by simp) (by simp)]
  · simp only [hne, ite_false, Fin.val_succ, Fin.val_castSucc, true_and]
    split_ifs <;> ring
  · have h1 : t ≠ i.castSucc := ht.1
    have h2 : ¬ ((t : ℕ) = (i : ℕ) + 1 ∧ k ≤ (i : ℕ)) := fun h =>
      ht.2 (Fin.ext (by simp only [Fin.val_succ]; omega))
    simp [h1, h2]

/-- The last entry of $L_k(\alpha)^T a$ is the last entry of $a$. -/
private theorem transpose_lowerBidiag_mulVec_last (k : ℕ) (α : ℝ) (a : Fin (n + 1) → ℝ) :
    ((BjorckPereyra.lowerBidiag n k α)ᵀ *ᵥ a) (Fin.last n) = a (Fin.last n) := by
  simp only [mulVec, dotProduct, transpose_apply, BjorckPereyra.lowerBidiag, of_apply]
  rw [Finset.sum_eq_single (Fin.last n) (fun t _ ht => ?_) (by simp)]
  · simp
  · have h2 : ¬ ((t : ℕ) = n + 1 ∧ k ≤ n) := fun h => by
      have := t.isLt
      omega
    simp [ht, h2]

/-- The loop $a_i \leftarrow a_i - a_{i+1} \alpha$ for $i = k, \dots, n-1$ computes
$a \leftarrow L_k(\alpha)^T a$. -/
private theorem sweep_transpose_lowerBidiag (k : Fin n) (α : ℝ) (a : Fin (n + 1) → ℝ) :
    ((List.finRange n).filter (fun i : Fin n => k ≤ i)).foldl
        (fun (a : Fin (n + 1) → ℝ) (i : Fin n) =>
          Function.update a i.castSucc (a i.castSucc - a i.succ * α)) a =
      (BjorckPereyra.lowerBidiag n k α)ᵀ *ᵥ a := by
  obtain ⟨h1, h2⟩ := foldl_update_eq Fin.castSucc
    (fun (i : Fin n) (g : Fin (n + 1) → ℝ) => g i.castSucc - g i.succ * α)
    ((List.finRange n).filter (fun i : Fin n => k ≤ i))
    ((pairwise_filter_le k).imp fun {a b} hab => by
      refine ⟨fun h => (ne_of_lt hab) (Fin.castSucc_injective _ h), fun g g' hg => ?_⟩
      have e1 : b.castSucc ≠ a.castSucc := fun h => (ne_of_lt hab) (Fin.castSucc_injective _ h).symm
      have e2 : b.succ ≠ a.castSucc := fun h => by
        have := congrArg Fin.val h
        simp only [Fin.val_castSucc, Fin.val_succ] at this
        have := Fin.lt_def.1 hab
        omega
      simp only [hg _ e1, hg _ e2]) a
  ext j
  induction j using Fin.lastCases with
  | last =>
    rw [transpose_lowerBidiag_mulVec_last,
      h2 _ fun i _ h => (Fin.castSucc_ne_last i) h]
  | cast i =>
    rw [transpose_lowerBidiag_mulVec_castSucc]
    by_cases hk : (k : ℕ) ≤ (i : ℕ)
    · rw [h1 i (mem_filter_le.2 (Fin.le_def.2 hk)), ite_eq_left hk]
    · rw [h2 _ fun i' hi' h => hk (by
          rw [mem_filter_le, Fin.le_def] at hi'
          rw [← Fin.castSucc_injective _ h]
          exact hi'), ite_eq_right hk]

/-- The exact run of Algorithm 4.6.1 is its two sweeps, written as loops of updates. -/
private theorem algorithm_4_6_1_id (x f : Fin (n + 1) → ℝ) :
    Id.run (algorithm_4_6_1 pure x f) =
      (List.finRange n).reverse.foldl (fun (a : Fin (n + 1) → ℝ) (k : Fin n) =>
        ((List.finRange n).filter (fun i : Fin n => k ≤ i)).foldl
          (fun (a : Fin (n + 1) → ℝ) (i : Fin n) =>
            Function.update a i.castSucc (a i.castSucc - a i.succ * x k.castSucc)) a)
        ((List.finRange n).foldl (fun (f : Fin (n + 1) → ℝ) (k : Fin n) =>
          ((List.finRange n).filter (fun i : Fin n => k ≤ i)).reverse.foldl
            (fun (f : Fin (n + 1) → ℝ) (i : Fin n) => Function.update f i.succ
              ((f i.succ - f i.castSucc) /
                (x i.succ - x ⟨(i : ℕ) - (k : ℕ), by have := i.isLt; omega⟩))) f) f) := by
  simp only [algorithm_4_6_1, pure_bind, List.foldlM_pure]
  rfl

/-- The node $x_k$ for `k : Fin n`, read through the cast from `ℕ` that the backbone factors use. -/
private theorem node_castSucc (x : Fin (n + 1) → ℝ) (k : Fin n) :
    x k.castSucc = x ((k : ℕ) : Fin (n + 1)) := by
  rw [← Fin.val_castSucc, Fin.cast_val_eq_self]

/-- **Algorithm 4.6.1** of [golub2013matrix], exact correctness. Let
$x_0, \dots, x_n \in \mathbb{R}$ be distinct, and let $f \in \mathbb{R}^{n+1}$. In exact
arithmetic, Algorithm 4.6.1 returns a vector $a$ with
$$V(x_0, \dots, x_n)^T a = f.$$

The first sweep computes $U^T f$, one factor $D_k^{-1} L_k(1)$ per pass, and the second sweep
computes $L^T$ of the result; then `GolubVanLoan.Chapter04.vandermonde_inv_factorization` gives
$V^{-T} = L^T U^T$. -/
theorem algorithm_4_6_1_spec {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (f : Fin (n + 1) → ℝ) :
    (vandermondeCols x)ᵀ *ᵥ Id.run (algorithm_4_6_1 pure x f) = f := by
  rw [algorithm_4_6_1_id]
  simp only [sweep_divDiff hx, sweep_transpose_lowerBidiag]
  simp only [node_castSucc x]
  rw [foldl_finRange (fun f k => ((BjorckPereyra.diffScale x k)⁻¹ *
      BjorckPereyra.lowerBidiag n k 1) *ᵥ f),
    foldl_finRange_reverse (fun a k => (BjorckPereyra.lowerBidiag n k (x k))ᵀ *ᵥ a),
    ← reverse_prod_mulVec, ← reverse_prod_mulVec, List.map_reverse, List.reverse_reverse]
  have hU : BjorckPereyra.upperFactorT x = ((List.range n).map fun k =>
      (BjorckPereyra.diffScale x k)⁻¹ * BjorckPereyra.lowerBidiag n k 1).reverse.prod := rfl
  have hL : BjorckPereyra.lowerFactorT x = ((List.range n).map fun k =>
      (BjorckPereyra.lowerBidiag n k (x k))ᵀ).prod := rfl
  rw [← hU, ← hL, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc,
    ← (vandermonde_inv_factorization hx).2.2.1, ← transpose_mul,
    nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 ((vandermonde_isUnit_iff x).2 hx)),
    transpose_one, one_mulVec]

/-- The loop $b_i \leftarrow b_i - \alpha b_{i-1}$ for $i = n, \dots, k+1$ computes
$b \leftarrow L_k(\alpha) b$. -/
private theorem sweep_lowerBidiag (k : Fin n) (α : ℝ) (b : Fin (n + 1) → ℝ) :
    ((List.finRange n).filter (fun i : Fin n => k ≤ i)).reverse.foldl
        (fun (b : Fin (n + 1) → ℝ) (i : Fin n) =>
          Function.update b i.succ (b i.succ - α * b i.castSucc)) b =
      BjorckPereyra.lowerBidiag n k α *ᵥ b := by
  obtain ⟨h1, h2⟩ := foldl_update_eq Fin.succ
    (fun (i : Fin n) (g : Fin (n + 1) → ℝ) => g i.succ - α * g i.castSucc)
    ((List.finRange n).filter (fun i : Fin n => k ≤ i)).reverse
    (List.pairwise_reverse.2 ((pairwise_filter_le k).imp fun {a b} hab => by
      refine ⟨fun h => (ne_of_lt hab) (Fin.succ_injective _ h).symm, fun g g' hg => ?_⟩
      have e1 : a.succ ≠ b.succ := fun h => (ne_of_lt hab) (Fin.succ_injective _ h)
      have e2 : a.castSucc ≠ b.succ := fun h => by
        have := congrArg Fin.val h
        simp only [Fin.val_castSucc, Fin.val_succ] at this
        have := Fin.lt_def.1 hab
        omega
      simp only [hg _ e1, hg _ e2])) b
  ext j
  rw [BjorckPereyra.lowerBidiag_mulVec_apply]
  by_cases hj : (k : ℕ) + 1 ≤ (j : ℕ)
  · have hj0 : (j : ℕ) - 1 < n := by have := j.isLt; omega
    set i : Fin n := ⟨(j : ℕ) - 1, hj0⟩
    have e1 : i.succ = j := Fin.ext (by simp [i]; omega)
    have hi : i ∈ ((List.finRange n).filter (fun i : Fin n => k ≤ i)).reverse := by
      rw [List.mem_reverse, mem_filter_le, Fin.le_def]
      simp [i]
      omega
    conv_lhs => rw [← e1]
    rw [h1 i hi, dite_eq_left hj]
    have e2 : i.castSucc = ⟨(j : ℕ) - 1, by omega⟩ := Fin.ext (by simp [i])
    rw [e1, e2]
  · rw [h2 j fun i hi h => hj (by
      rw [List.mem_reverse, mem_filter_le, Fin.le_def] at hi
      rw [← h, Fin.val_succ]
      omega), dite_eq_right hj]

/-- For distinct nodes, the loop $b_i \leftarrow b_i / (x_i - x_{i-k-1})$ for $i = k+1, \dots, n$
computes $b \leftarrow D_k^{-1} b$. -/
private theorem sweep_diffScale {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) (k : Fin n)
    (b : Fin (n + 1) → ℝ) :
    ((List.finRange n).filter (fun i : Fin n => k ≤ i)).foldl
        (fun (b : Fin (n + 1) → ℝ) (i : Fin n) => Function.update b i.succ
          (b i.succ / (x i.succ - x ⟨(i : ℕ) - (k : ℕ), by have := i.isLt; omega⟩))) b =
      (BjorckPereyra.diffScale x k)⁻¹ *ᵥ b := by
  obtain ⟨h1, h2⟩ := foldl_update_eq Fin.succ
    (fun (i : Fin n) (g : Fin (n + 1) → ℝ) =>
      g i.succ / (x i.succ - x ⟨(i : ℕ) - (k : ℕ), by have := i.isLt; omega⟩))
    ((List.finRange n).filter (fun i : Fin n => k ≤ i))
    ((pairwise_filter_le k).imp fun {a b} hab => by
      refine ⟨fun h => (ne_of_lt hab) (Fin.succ_injective _ h), fun g g' hg => ?_⟩
      have e1 : b.succ ≠ a.succ := fun h => (ne_of_lt hab) (Fin.succ_injective _ h).symm
      simp only [hg _ e1]) b
  ext j
  rw [BjorckPereyra.inv_diffScale hx, mulVec_diagonal]
  by_cases hj : (k : ℕ) + 1 ≤ (j : ℕ)
  · have hj0 : (j : ℕ) - 1 < n := by have := j.isLt; omega
    set i : Fin n := ⟨(j : ℕ) - 1, hj0⟩
    have e1 : i.succ = j := Fin.ext (by simp [i]; omega)
    have hi : i ∈ (List.finRange n).filter (fun i : Fin n => k ≤ i) := by
      rw [mem_filter_le, Fin.le_def]
      simp [i]
      omega
    conv_lhs => rw [← e1]
    rw [h1 i hi, ite_eq_right (by omega), div_eq_inv_mul]
    have e3 : (⟨(i : ℕ) - (k : ℕ), by have := i.isLt; omega⟩ : Fin (n + 1)) =
        ⟨(j : ℕ) - k - 1, by omega⟩ := Fin.ext (by simp [i]; omega)
    rw [e1, e3]
  · rw [h2 j fun i hi h => hj (by
      rw [mem_filter_le, Fin.le_def] at hi
      rw [← h, Fin.val_succ]
      omega), ite_eq_left (by omega), inv_one, one_mul]

/-- The exact run of Algorithm 4.6.2 is its sweeps, written as loops of updates. -/
private theorem algorithm_4_6_2_id (x b : Fin (n + 1) → ℝ) :
    Id.run (algorithm_4_6_2 pure x b) =
      (List.finRange n).reverse.foldl (fun (b : Fin (n + 1) → ℝ) (k : Fin n) =>
        ((List.finRange n).filter (fun i : Fin n => k ≤ i)).foldl
          (fun (b : Fin (n + 1) → ℝ) (i : Fin n) =>
            Function.update b i.castSucc (b i.castSucc - b i.succ))
          (((List.finRange n).filter (fun i : Fin n => k ≤ i)).foldl
            (fun (b : Fin (n + 1) → ℝ) (i : Fin n) => Function.update b i.succ
              (b i.succ / (x i.succ - x ⟨(i : ℕ) - (k : ℕ), by have := i.isLt; omega⟩))) b))
        ((List.finRange n).foldl (fun (b : Fin (n + 1) → ℝ) (k : Fin n) =>
          ((List.finRange n).filter (fun i : Fin n => k ≤ i)).reverse.foldl
            (fun (b : Fin (n + 1) → ℝ) (i : Fin n) =>
              Function.update b i.succ (b i.succ - x k.castSucc * b i.castSucc)) b) b) := by
  simp only [algorithm_4_6_2, pure_bind, List.foldlM_pure]
  rfl

/-- **Algorithm 4.6.2** of [golub2013matrix], exact correctness. Let
$x_0, \dots, x_n \in \mathbb{R}$ be distinct, and let $b \in \mathbb{R}^{n+1}$. In exact
arithmetic, Algorithm 4.6.2 returns a vector $z$ with
$$V(x_0, \dots, x_n) z = b.$$

The first sweep applies $L = L_{n-1}(x_{n-1}) \cdots L_0(x_0)$ and the second applies $U =
L_0(1)^T D_0^{-1} \cdots L_{n-1}(1)^T D_{n-1}^{-1}$, so that $z = ULb = V^{-1} b$ by
`GolubVanLoan.Chapter04.vandermonde_inv_factorization`. -/
theorem algorithm_4_6_2_spec {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (b : Fin (n + 1) → ℝ) :
    vandermondeCols x *ᵥ Id.run (algorithm_4_6_2 pure x b) = b := by
  have hsub : (fun (b : Fin (n + 1) → ℝ) (i : Fin n) =>
      Function.update b i.castSucc (b i.castSucc - b i.succ)) =
      fun b i => Function.update b i.castSucc (b i.castSucc - b i.succ * 1) := by
    simp only [mul_one]
  rw [algorithm_4_6_2_id, hsub]
  simp only [sweep_lowerBidiag, sweep_diffScale hx, sweep_transpose_lowerBidiag, mulVec_mulVec]
  simp only [node_castSucc x]
  rw [foldl_finRange (fun b k => BjorckPereyra.lowerBidiag n k (x k) *ᵥ b),
    foldl_finRange_reverse (fun b k => ((BjorckPereyra.lowerBidiag n k 1)ᵀ *
      (BjorckPereyra.diffScale x k)⁻¹) *ᵥ b),
    ← reverse_prod_mulVec, ← reverse_prod_mulVec, List.map_reverse, List.reverse_reverse]
  have hL : (BjorckPereyra.lowerFactorT x)ᵀ = ((List.range n).map fun k =>
      BjorckPereyra.lowerBidiag n k (x k)).reverse.prod := by
    rw [BjorckPereyra.lowerFactorT, transpose_list_prod, List.map_map]
    simp only [Function.comp_def, transpose_transpose]
  have hU : (BjorckPereyra.upperFactorT x)ᵀ = ((List.range n).map fun k =>
      (BjorckPereyra.lowerBidiag n k 1)ᵀ * (BjorckPereyra.diffScale x k)⁻¹).prod := by
    rw [BjorckPereyra.upperFactorT, transpose_list_prod, List.map_reverse,
      List.reverse_reverse, List.map_map]
    congr 2
    funext k
    rw [Function.comp_apply, transpose_mul, transpose_nonsing_inv, BjorckPereyra.diffScale,
      diagonal_transpose]
  rw [← hL, ← hU, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc,
    ← (vandermonde_inv_factorization hx).2.2.2,
    mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 ((vandermonde_isUnit_iff x).2 hx)),
    one_mulVec]

end GolubVanLoan.Chapter04
