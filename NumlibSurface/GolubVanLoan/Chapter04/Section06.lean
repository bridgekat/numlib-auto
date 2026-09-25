import Numlib.Direct.Vandermonde
import NumlibSurface.GolubVanLoan.Chapter01.Section04

/-!
# Golub–Van Loan §4.6: Vandermonde systems

Surface file for [golub2013matrix] §4.6: the Vandermonde matrix `V(x₀, …, x_n)`, the equivalence of
`Vᵀ a = f` with polynomial interpolation (4.6.1), the Newton form of the interpolant (4.6.2), the
factorization `V⁻ᵀ = Lᵀ Uᵀ` that the Björck–Pereyra algorithms compute implicitly (§4.6.2), and
Algorithms 4.6.1 (`Vᵀ a = f`) and 4.6.2 (`V z = b`) with their exact specifications.

## Conventions

The book indexes from `0` in this section, and so does this file: nodes `x : Fin (n + 1) → ℝ`,
distinct (`Function.Injective x`). The book's `V(x₀, …, x_n)`, whose *columns* are the powers of
the nodes, is `vandermonde x = (Matrix.vandermonde x)ᵀ` (Mathlib's rows are the nodes). The book's
elementary bidiagonal `L_k(α)` and diagonal `D_k` are the backbone's
`BjorckPereyra.lowerBidiag n k α` and `BjorckPereyra.diffScale x k`; its
`Uᵀ = D_{n−1}⁻¹ L_{n−1}(1) ⋯ D_0⁻¹ L_0(1)` and `Lᵀ = L_0(x_0)ᵀ ⋯ L_{n−1}(x_{n−1})ᵀ` are
`BjorckPereyra.upperFactorT x` and `BjorckPereyra.lowerFactorT x`.

The algorithms follow the algorithm conventions of `NumlibSurface/GolubVanLoan`: every difference,
product and quotient passes through the rounding hook `rnd`, the differences of nodes included. The
inner loops run over the index lists of the book, `i = n:−1:k+1` as the reversed list of the
`i : Fin n` with `k ≤ i` acting on entry `i.succ` (so `i − 1` is `i.castSucc`), `i = k:n−1` as
that list in increasing order acting on entry `i.castSucc` (so `i + 1` is `i.succ`); the loop
orders make every step read values not yet overwritten, and the exact runs are the products of
the book's factors.

## Sources

Backbone `Numlib/Direct/Vandermonde` (`BjorckPereyra`), `Numlib/Approximation/NewtonForm`
(`DividedDifference`), Mathlib's `Matrix.vandermonde`, `Matrix.det_vandermonde_ne_zero_iff`,
`Lagrange.interpolate`. Chapter 1's `fourierMatrix` for the DFT remark. The stages (4.6.3)–(4.6.4)
of Algorithm 4.6.1 are not separate results; the accuracy remark of Björck and Pereyra and the
confluent Vandermonde systems are not formalized.
-/

open Matrix hiding vandermonde
open Polynomial Finset
open scoped Fin.NatCast

namespace GolubVanLoan.Chapter04

variable {n : ℕ}

/-! ### §4.6 The Vandermonde matrix -/

/-- **§4.6, the Vandermonde matrix.** "A matrix `V ∈ ℝ^{(n+1)×(n+1)}` of the form
`V = V(x₀, …, x_n) = [1 1 ⋯ 1; x₀ x₁ ⋯ x_n; ⋮; x₀ⁿ x₁ⁿ ⋯ x_nⁿ]` is said to be a Vandermonde
matrix": entry `(i, j)` is `x_j ^ i`, the transpose of Mathlib's `Matrix.vandermonde x`. -/
def vandermonde (x : Fin (n + 1) → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  (Matrix.vandermonde x)ᵀ

/-- The entries of `V(x₀, …, x_n)`: `V i j = x_j ^ i`. -/
theorem vandermonde_apply (x : Fin (n + 1) → ℝ) (i j : Fin (n + 1)) :
    vandermonde x i j = x j ^ (i : ℕ) := rfl

/-- **§4.6.** "Note that the discrete Fourier transform matrix (§1.4.1) is a very special complex
Vandermonde matrix": `F_n = (ω_n^{kj})` is the Vandermonde matrix of the nodes `ω_n^k`,
`ω_n = exp(−2πi/n)` (symmetric, so it is also its transpose). -/
theorem dft_eq_vandermonde (n : ℕ) :
    Chapter01.fourierMatrix n =
      Matrix.vandermonde fun k : Fin n => Complex.exp (-2 * Real.pi * Complex.I / n) ^ (k : ℕ) := by
  ext k j
  rw [Chapter01.fourierMatrix_apply, Matrix.vandermonde_apply, ← pow_mul]

/-! ### §4.6.1 Polynomial interpolation: `Vᵀ a = f` -/

/-- **(4.6.1).** "Solving `Vᵀ a = f` is equivalent to polynomial interpolation. This follows because
if `Vᵀ a = f` and `p(x) = ∑_{j=0}^{n} a_j x^j`, then `p(x_i) = f_i` for `i = 0:n`" (and
conversely). -/
theorem equation_4_6_1 (x a f : Fin (n + 1) → ℝ) :
    (vandermonde x)ᵀ *ᵥ a = f ↔ ∀ i, (∑ j, C (a j) * X ^ (j : ℕ)).eval (x i) = f i := by
  rw [vandermonde, transpose_transpose, funext_iff]
  simp only [Matrix.vandermonde_mulVec_eq_eval]

/-- **§4.6.1.** "Consequently, `V` is nonsingular as long as the `x_i` are distinct" — and only
then. -/
theorem vandermonde_isUnit_iff (x : Fin (n + 1) → ℝ) :
    IsUnit (vandermonde x) ↔ Function.Injective x := by
  rw [isUnit_iff_isUnit_det, vandermonde, det_transpose, isUnit_iff_ne_zero,
    Matrix.det_vandermonde_ne_zero_iff]

/-- **(4.6.2).** "The first step in computing the `a_j` of (4.6.1) is to calculate the Newton
representation of the interpolating polynomial `p`:
`p(x) = ∑_{k=0}^{n} c_k (∏_{i=0}^{k−1} (x − x_i))`. The constants `c_k` are divided
differences": for distinct nodes, the interpolant of the data `f_i = g(x_i)` has Newton
coefficients `c_k = g[x₀, …, x_k]`. -/
theorem equation_4_6_2 {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) (g : ℝ → ℝ) :
    Lagrange.interpolate univ x (fun i => g (x i)) =
      ∑ k, C (DividedDifference.newtonOn (Iic k) x g) * ∏ i ∈ Iio k, (X - C (x i)) := by
  rw [DividedDifference.interpolate_eq_sum_newtonOn_mul_nodal (s := univ) hx.injOn g]
  refine sum_congr rfl fun k _ => ?_
  have hle : ({i ∈ univ | i ≤ k} : Finset (Fin (n + 1))) = Iic k := by ext; simp
  have hlt : ({i ∈ univ | i < k} : Finset (Fin (n + 1))) = Iio k := by ext; simp
  rw [hle, hlt, Lagrange.nodal]

/-! ### §4.6.2 The factorization `V⁻ᵀ = Lᵀ Uᵀ` -/

/-- **§4.6.2.** "It is easy to verify from (4.6.3) that, if `f = f(0:n)` and `c = c(0:n)` is the
vector of divided differences, then `c = Uᵀ f` … Similarly, from (4.6.4) we have `a = Lᵀ c` … Thus,
`V⁻ᵀ = Lᵀ Uᵀ`, which shows that Algorithm 4.6.1 solves `Vᵀ a = f` by tacitly computing the 'UL
factorization' of `V⁻¹`": with `Uᵀ = BjorckPereyra.upperFactorT x` and
`Lᵀ = BjorckPereyra.lowerFactorT x`, for distinct nodes, `Uᵀ` maps data to divided differences,
`Lᵀ` maps Newton coefficients to monomial coefficients, `V⁻ᵀ = Lᵀ Uᵀ` and `V⁻¹ = U L`. -/
theorem vandermonde_inv_factorization {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) :
    (∀ (g : ℝ → ℝ) (k : Fin (n + 1)), (BjorckPereyra.upperFactorT x *ᵥ fun j => g (x j)) k =
      DividedDifference.newtonOn (Iic k) x g) ∧
    (∀ c : Fin (n + 1) → ℝ, ∑ j, C ((BjorckPereyra.lowerFactorT x *ᵥ c) j) * X ^ (j : ℕ) =
      ∑ k : Fin (n + 1), C (c k) * ∏ i ∈ range k, (X - C (x i))) ∧
    (vandermonde x)⁻¹ᵀ = BjorckPereyra.lowerFactorT x * BjorckPereyra.upperFactorT x ∧
    (vandermonde x)⁻¹ = (BjorckPereyra.upperFactorT x)ᵀ * (BjorckPereyra.lowerFactorT x)ᵀ := by
  refine ⟨fun g k => BjorckPereyra.upperFactorT_mulVec_eq_newtonOn hx g k,
    fun c => BjorckPereyra.lowerFactorT_mulVec_newtonCoeff x c, ?_, ?_⟩
  · rw [vandermonde, ← transpose_nonsing_inv, transpose_transpose,
      BjorckPereyra.inv_vandermonde_eq hx]
  · rw [vandermonde, ← transpose_nonsing_inv, BjorckPereyra.inv_vandermonde_eq hx, transpose_mul]

/-! ### Algorithms 4.6.1 and 4.6.2 -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 4.6.1.** "Given `x(0:n) ∈ ℝ^{n+1}` with distinct entries and `f = f(0:n) ∈ ℝ^{n+1}`,
the following algorithm overwrites `f` with the solution `a = a(0:n)` to the Vandermonde system
`V(x₀, …, x_n)ᵀ a = f`":
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
The differences of nodes are computed, hence rounded. -/
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

/-- **Algorithm 4.6.2.** "Given `x(0:n) ∈ ℝ^{n+1}` with distinct entries and `b = b(0:n) ∈ ℝ^{n+1}`,
the following algorithm overwrites `b` with the solution `z = z(0:n)` to the Vandermonde system
`V(x₀, …, x_n) z = b`":
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
``` -/
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

/-! #### Exact semantics -/

/-- A loop of updates in which every step reads only entries that earlier steps do not write:
each written entry holds the value computed from the initial state, the others are unchanged. -/
private theorem foldl_update_eq {ι κ β : Type*} [DecidableEq κ] (w : ι → κ)
    (h : ι → (κ → β) → β) (l : List ι)
    (hl : l.Pairwise fun a b => w a ≠ w b ∧
      ∀ g g' : κ → β, (∀ t, t ≠ w a → g t = g' t) → h b g = h b g') (f : κ → β) :
    (∀ i ∈ l, l.foldl (fun g i => Function.update g (w i) (h i g)) f (w i) = h i f) ∧
      ∀ t, (∀ i ∈ l, w i ≠ t) →
        l.foldl (fun g i => Function.update g (w i) (h i g)) f t = f t := by
  induction l generalizing f with
  | nil => exact ⟨fun _ hi => absurd hi List.not_mem_nil, fun _ _ => rfl⟩
  | cons a l ih =>
    obtain ⟨hal, hl'⟩ := List.pairwise_cons.1 hl
    obtain ⟨ih1, ih2⟩ := ih hl' (Function.update f (w a) (h a f))
    have hagree : ∀ t, t ≠ w a → Function.update f (w a) (h a f) t = f t :=
      fun t ht => Function.update_of_ne ht _ _
    refine ⟨fun i hi => ?_, fun t ht => ?_⟩
    · rw [List.foldl_cons]
      rcases List.mem_cons.1 hi with rfl | hi
      · rw [ih2 (w i) fun j hj => (hal j hj).1.symm, Function.update_self]
      · rw [ih1 i hi]
        exact (hal i hi).2 _ _ hagree
    · rw [List.foldl_cons, ih2 t fun j hj => ht j (List.mem_cons_of_mem _ hj)]
      exact hagree t (ht a List.mem_cons_self).symm

/-- `(l.map S).reverse.prod`, the product `S_{k_r} ⋯ S_{k_1}`, applied to `f` is the loop applying
`S_{k_1}`, then `S_{k_2}`, …. -/
private theorem reverse_prod_mulVec {α : Type*} (S : α → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (l : List α) (f : Fin (n + 1) → ℝ) :
    (l.map S).reverse.prod *ᵥ f = l.foldl (fun f k => S k *ᵥ f) f := by
  induction l generalizing f with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.reverse_cons, List.prod_append, List.prod_singleton, ← mulVec_mulVec,
      ih, List.foldl_cons]

/-- `(l.map S).prod`, the product `S_{k_1} ⋯ S_{k_r}`, applied to `f` is the loop over the reversed
list. -/
private theorem prod_mulVec {α : Type*} (S : α → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (l : List α) (f : Fin (n + 1) → ℝ) :
    (l.map S).prod *ᵥ f = l.reverse.foldl (fun f k => S k *ᵥ f) f := by
  rw [← List.reverse_reverse (l.map S), ← List.map_reverse, reverse_prod_mulVec]

/-- A loop over `k : Fin n` is the loop over the values `k : ℕ < n`. -/
private theorem foldl_finRange {β : Type*} (g : β → ℕ → β) (b : β) :
    (List.finRange n).foldl (fun b (k : Fin n) => g b k) b = (List.range n).foldl g b := by
  rw [← List.map_coe_finRange_eq_range, List.foldl_map]

/-- The reversed form of `foldl_finRange`. -/
private theorem foldl_finRange_reverse {β : Type*} (g : β → ℕ → β) (b : β) :
    (List.finRange n).reverse.foldl (fun b (k : Fin n) => g b k) b =
      (List.range n).reverse.foldl g b := by
  rw [← List.map_coe_finRange_eq_range, ← List.map_reverse, List.foldl_map]

/-- The indices `i : Fin n` with `k ≤ i`, in increasing order. -/
private theorem pairwise_filter_le (k : Fin n) :
    ((List.finRange n).filter fun i : Fin n => k ≤ i).Pairwise (· < ·) :=
  (List.pairwise_lt_finRange n).filter _

private theorem mem_filter_le {k i : Fin n} :
    i ∈ (List.finRange n).filter (fun i : Fin n => k ≤ i) ↔ k ≤ i := by simp

/-- The first sweep of Algorithm 4.6.1, one pass: `f ← D_k⁻¹ L_k(1) f`. -/
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

/-- The action of `L_k(α)ᵀ` below the last entry: `(L_k(α)ᵀ a)_i = a_i − α a_{i+1}` for `i ≥ k`. -/
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

/-- The action of `L_k(α)ᵀ` on the last entry: it is unchanged. -/
private theorem transpose_lowerBidiag_mulVec_last (k : ℕ) (α : ℝ) (a : Fin (n + 1) → ℝ) :
    ((BjorckPereyra.lowerBidiag n k α)ᵀ *ᵥ a) (Fin.last n) = a (Fin.last n) := by
  simp only [mulVec, dotProduct, transpose_apply, BjorckPereyra.lowerBidiag, of_apply]
  rw [Finset.sum_eq_single (Fin.last n) (fun t _ ht => ?_) (by simp)]
  · simp
  · have h2 : ¬ ((t : ℕ) = n + 1 ∧ k ≤ n) := fun h => by
      have := t.isLt
      omega
    simp [ht, h2]

/-- The upward loop `a(i) ← a(i) − a(i+1) α`, `i = k:n−1`: `a ← L_k(α)ᵀ a`. -/
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

/-- The exact run of Algorithm 4.6.1 is its two sweeps as loops of updates. -/
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

/-- The node `x k` read through the `ℕ`-indexing of the backbone factors. -/
private theorem node_castSucc (x : Fin (n + 1) → ℝ) (k : Fin n) :
    x k.castSucc = x ((k : ℕ) : Fin (n + 1)) := by
  rw [← Fin.val_castSucc, Fin.cast_val_eq_self]

/-- **Exact correctness of Algorithm 4.6.1**: for distinct nodes, the exact run solves the
Vandermonde system `V(x₀, …, x_n)ᵀ a = f`. The first sweep computes `Uᵀ f` (one factor
`D_k⁻¹ L_k(1)` per pass, the downward inner order reading only old values), the second `Lᵀ` of
that; `V⁻ᵀ = Lᵀ Uᵀ` (`vandermonde_inv_factorization`). -/
theorem algorithm_4_6_1_spec {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (f : Fin (n + 1) → ℝ) :
    (vandermonde x)ᵀ *ᵥ Id.run (algorithm_4_6_1 pure x f) = f := by
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

/-- The downward loop `b(i) ← b(i) − x(k) b(i−1)`, `i = n:−1:k+1`: `b ← L_k(x_k) b`. -/
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

/-- The loop `b(i) ← b(i) / (x(i) − x(i−k−1))`, `i = k+1:n`: `b ← D_k⁻¹ b`. -/
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

/-- The exact run of Algorithm 4.6.2 is its sweeps as loops of updates. -/
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

/-- **Exact correctness of Algorithm 4.6.2**: for distinct nodes, the exact run solves
`V(x₀, …, x_n) z = b`. The first sweep applies `L = L_{n−1}(x_{n−1}) ⋯ L_0(x_0)`, the second
`U = L_0(1)ᵀ D_0⁻¹ ⋯ L_{n−1}(1)ᵀ D_{n−1}⁻¹`, so `z = U L b = V⁻¹ b`
(`vandermonde_inv_factorization`). -/
theorem algorithm_4_6_2_spec {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (b : Fin (n + 1) → ℝ) :
    vandermonde x *ᵥ Id.run (algorithm_4_6_2 pure x b) = b := by
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
