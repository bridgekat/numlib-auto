import Mathlib.LinearAlgebra.Vandermonde
import Numlib.Approximation.NewtonForm

/-!
# Vandermonde systems and the Björck–Pereyra factorization

The Vandermonde system `Vᵀ a = f` of polynomial interpolation and its fast solution by the
Björck–Pereyra algorithm ([golub2013matrix] §4.6; Björck and Pereyra 1970; [higham2002accuracy]
§22.2).

Mathlib's `Matrix.vandermonde x : Matrix (Fin (n + 1)) (Fin (n + 1)) K` has entries `x i ^ j` (the
nodes index the rows); the book's `V(x₀, …, x_n)` is its transpose. The interpolation system of the
book is therefore `vandermonde x *ᵥ a = f`: the polynomial with coefficients `a` takes the values
`f` at the nodes (`Matrix.vandermonde_mulVec_eq_eval`).

Björck and Pereyra solve it in two sweeps, each a product of elementary bidiagonal matrices
`L_k(α)` (`BjorckPereyra.lowerBidiag`) and diagonal matrices `D_k` (`BjorckPereyra.diffScale`):

* the **divided-difference sweep** `c = Uᵀ f`, `Uᵀ = D_{n−1}⁻¹ L_{n−1}(1) ⋯ D_0⁻¹ L_0(1)`
  (`BjorckPereyra.upperFactorT`), computes the coefficients `c_k = f[x₀, …, x_k]` of the Newton
  form of the interpolant (`BjorckPereyra.upperFactorT_mulVec_eq_newtonOn`);
* the **Newton-to-monomial sweep** `a = Lᵀ c`, `Lᵀ = L_0(x_0)ᵀ ⋯ L_{n−1}(x_{n−1})ᵀ`
  (`BjorckPereyra.lowerFactorT`), converts a Newton form to monomial coefficients
  (`BjorckPereyra.lowerFactorT_mulVec_newtonCoeff`).

Together they give **`V⁻ᵀ = Lᵀ Uᵀ`** (`BjorckPereyra.inv_vandermonde_eq`), which is what the
surface Algorithms 4.6.1–4.6.2 are proved against.

## Design

The second sweep is proved as a statement about row vectors, uniformly in a commutative ring:
the row of powers `(1, t, …, tⁿ)` times `Lᵀ` is the row of Newton basis values
`(∏_{l<j} (t − x_l))_j` (`BjorckPereyra.pow_vecMul_lowerFactorT`). At `t = x_i` this is the
product `V Lᵀ` (`BjorckPereyra.vandermonde_mul_lowerFactorT`), and at `t = X` over the polynomial
ring it is the polynomial identity of the Newton-to-monomial conversion. The first sweep is proved
by induction on the number of factors applied, with the divided differences over the windows
`[i − k, i]` of consecutive nodes (`ℕ`-indexed, truncated at `0`) as invariant.

## References

* [golub2013matrix] §4.6.
* [higham2002accuracy] §22.2.
-/

open Matrix Polynomial Finset

open scoped Fin.NatCast

/-- **Vandermonde systems are interpolation problems** ([golub2013matrix] (4.6.1)): the `i`-th
entry of `vandermonde x *ᵥ a` is the value at `x i` of the polynomial with coefficients `a`. -/
theorem Matrix.vandermonde_mulVec_eq_eval {R : Type*} [CommRing R] {n : ℕ} (x : Fin n → R)
    (a : Fin n → R) (i : Fin n) :
    (vandermonde x *ᵥ a) i = (∑ j, C (a j) * X ^ (j : ℕ)).eval (x i) := by
  simp only [mulVec, dotProduct, vandermonde_apply, eval_finsetSum, eval_mul, eval_C, eval_pow,
    eval_X, mul_comm]

namespace BjorckPereyra

section Ring

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The elementary lower bidiagonal matrix `L_k(α)` of [golub2013matrix] §4.6.2: the identity with
`-α` on the subdiagonal positions `(i + 1, i)` for `i ≥ k`. -/
def lowerBidiag (n k : ℕ) (α : R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  of fun i j => if i = j then 1 else if (i : ℕ) = j + 1 ∧ k ≤ (j : ℕ) then -α else 0

/-- `L_k(α)` subtracts `α` times the previous entry from every entry below position `k`. -/
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

/-- `L_k(α)ᵀ` acting on a row vector: `α` times the previous entry is subtracted from every entry
below position `k`. -/
theorem vecMul_transpose_lowerBidiag_apply (k : ℕ) (α : R) (w : Fin (n + 1) → R)
    (j : Fin (n + 1)) :
    (w ᵥ* (lowerBidiag n k α)ᵀ) j =
      if h : k + 1 ≤ (j : ℕ) then w j - α * w ⟨j - 1, by omega⟩ else w j := by
  rw [vecMul_transpose, lowerBidiag_mulVec_apply]

/-- The factor `Lᵀ = L_0(x_0)ᵀ ⋯ L_{n−1}(x_{n−1})ᵀ` of [golub2013matrix] §4.6.2, the
Newton-to-monomial sweep; its transpose is the book's unit lower triangular `L`. -/
def lowerFactorT (x : Fin (n + 1) → R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  ((List.range n).map fun k => (lowerBidiag n k (x k))ᵀ).prod

/-- The partial products `L_0(x_0)ᵀ ⋯ L_{k−1}(x_{k−1})ᵀ`. -/
private def lowerFactorTPartial (x : Fin (n + 1) → R) (k : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  ((List.range k).map fun k => (lowerBidiag n k (x k))ᵀ).prod

private theorem lowerFactorTPartial_succ (x : Fin (n + 1) → R) (k : ℕ) :
    lowerFactorTPartial x (k + 1) = lowerFactorTPartial x k * (lowerBidiag n k (x k))ᵀ := by
  simp [lowerFactorTPartial, List.range_succ]

/-- The row of powers after `k` factors of the second sweep. -/
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

/-- **The Newton-to-monomial sweep, row form** ([golub2013matrix] (4.6.4)): the row of powers
`(1, t, …, tⁿ)` times `Lᵀ` is the row of Newton basis values `(∏_{l<j} (t − x_l))_j`, in any
commutative ring. -/
theorem pow_vecMul_lowerFactorT (x : Fin (n + 1) → R) (t : R) (j : Fin (n + 1)) :
    ((fun j : Fin (n + 1) => t ^ (j : ℕ)) ᵥ* lowerFactorT x) j =
      ∏ l ∈ range j, (t - x l) := by
  have := pow_vecMul_lowerFactorTPartial x t le_rfl j
  rw [min_eq_left (by omega : (j : ℕ) ≤ n), Nat.sub_self, pow_zero, one_mul] at this
  exact this

/-- `V Lᵀ` is the Newton basis matrix: `(vandermonde x * lowerFactorT x) i j = ∏_{l<j} (x_i − x_l)`
([golub2013matrix] §4.6.2). -/
theorem vandermonde_mul_lowerFactorT (x : Fin (n + 1) → R) :
    vandermonde x * lowerFactorT x = of fun i (j : Fin (n + 1)) => ∏ l ∈ range j, (x i - x l) := by
  ext i j
  rw [of_apply, ← pow_vecMul_lowerFactorT x (x i) j]
  rfl

/-- **The Newton-to-monomial sweep is `a = Lᵀ c`** ([golub2013matrix] (4.6.4) and the recursion
`p_k = c_k + (x − x_k) p_{k+1}` before it): the polynomial with coefficients `Lᵀ c` is the Newton
form `∑_k c_k ∏_{i<k} (X − x_i)`. -/
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

/-- The nodes as an `ℕ`-indexed family (the last node repeated past the end is never read). -/
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

/-- The diagonal factor `D_k = diag(1, …, 1, x_{k+1} − x_0, …, x_n − x_{n−k−1})` (`k + 1` ones) of
[golub2013matrix] §4.6.2. -/
def diffScale (x : Fin (n + 1) → K) (k : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  diagonal fun i => if (i : ℕ) ≤ k then 1 else x i - x ⟨i - k - 1, by omega⟩

/-- The factor `Uᵀ = D_{n−1}⁻¹ L_{n−1}(1) ⋯ D_0⁻¹ L_0(1)` of [golub2013matrix] §4.6.2, the
divided-difference sweep; its transpose is the book's upper triangular `U`. -/
noncomputable def upperFactorT (x : Fin (n + 1) → K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  ((List.range n).map fun k => (diffScale x k)⁻¹ * lowerBidiag n k 1).reverse.prod

/-- For distinct nodes, `D_k` is invertible with the reciprocal diagonal. -/
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

/-- The partial products `D_{k−1}⁻¹ L_{k−1}(1) ⋯ D_0⁻¹ L_0(1)`. -/
private noncomputable def upperFactorTPartial (x : Fin (n + 1) → K) (k : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  ((List.range k).map fun k => (diffScale x k)⁻¹ * lowerBidiag n k 1).reverse.prod

private theorem upperFactorTPartial_succ (x : Fin (n + 1) → K) (k : ℕ) :
    upperFactorTPartial x (k + 1) =
      (diffScale x k)⁻¹ * lowerBidiag n k 1 * upperFactorTPartial x k := by
  simp [upperFactorTPartial, List.range_succ]

/-- The invariant of the divided-difference sweep: after `k` factors, entry `i` holds the divided
difference over the window `[i − k, i]` (truncated at `0`). -/
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

/-- **The divided-difference sweep is `c = Uᵀ f`** ([golub2013matrix] §4.6.2, "it is easy to
verify from (4.6.3)"): for distinct nodes, `(Uᵀ f)_k = f[x₀, …, x_k]`, where `g` is any function
with `g (x i) = f i`. -/
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

/-- **The Björck–Pereyra factorization `V⁻ᵀ = Lᵀ Uᵀ`** ([golub2013matrix] §4.6.2): for distinct
nodes, `(vandermonde x)⁻¹ = lowerFactorT x * upperFactorT x` (the book's `V` is
`(vandermonde x)ᵀ`, so this is `V⁻ᵀ = Lᵀ Uᵀ`, and its transpose `V⁻¹ = U L` is what Algorithm
4.6.2 applies). -/
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
  simp only [mul_apply, of_apply, hcol, upperFactorT_mulVec_eq_newtonOn hx]
  -- Newton's formula evaluated at the node `x i`
  have hN := DividedDifference.interpolate_eq_sum_newtonOn_mul_nodal
    (s := (univ : Finset (Fin (n + 1)))) (hx.injOn) g
  have hv := congrArg (eval (x i)) hN
  rw [Lagrange.eval_interpolate_at_node _ hx.injOn (mem_univ i), eval_finsetSum] at hv
  simp only [eval_mul, eval_C, Lagrange.eval_nodal] at hv
  have h1 : g (x i) = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K) i j := by
    rw [congrFun hg i, one_apply]
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
