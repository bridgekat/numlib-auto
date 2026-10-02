/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Algebra.BigOperators.Group.List.Basic` (the monoid part) and
`Mathlib.LinearAlgebra.UnitaryGroup` (the matrix part).
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Data.List.OfFn
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.NoncommRing

/-!
# Ordered products of a sequence

The products of the first `r` terms of a sequence `P : ℕ → M` in a monoid, in the two orders in
which a sequence of transformations accumulates:

* `prodRev P r = P (r-1) * ⋯ * P 1 * P 0`, each new factor multiplying on the left — the
  accumulated transformation `Q_r` of `x_{k+1} = P_k x_k`, as in the backward error analysis of a
  sequence of Householder or Givens transformations ([higham2002accuracy] Lemma 19.3);
* `prodFwd P r = P 0 * P 1 * ⋯ * P (r-1)`, each new factor multiplying on the right — the
  orthogonal factor `Q = Q₁ ⋯ Q_r` of a factorization built one reflector at a time
  ([golub2013matrix] §5.1.6–5.1.7, the WY representations), or a sweep of plane rotations.

Both are recursions on `r`, so statements about them are inductions on `r` with no `Fin` casts;
`prodFwd_eq_prod_ofFn`, `prodRev_eq_prod_ofFn` and `prod_map_range'_eq_prodFwd` bridge them to the
list products `(List.ofFn fun j : Fin r => P j).prod`, its reverse, and
`((List.range' b n).map P).prod`.

The algebra of the products, each in both orders, is monoid algebra: they only read their first
`r` factors (`prodFwd_congr`), peel off their first factor (`prodFwd_succ'`), commute with what
commutes with their factors (`commute_prodFwd`), are invertible when their factors are
(`isUnit_prodFwd`), stay in a submonoid containing their factors (`prodFwd_mem`), are mapped
factorwise by a monoid homomorphism (`map_prodFwd`), and for involutions the two orders invert each
other (`prodFwd_mul_prodRev`). In a ring, a product of factors whose departures from the identity
annihilate each other is the identity plus the sum of the departures
(`prodFwd_eq_one_add_sum_sub_one`).

For matrices: the determinant of a product is the product of the determinants
(`Matrix.det_prodFwd`), the transpose of a forward product is the reverse product of the
transposes (`Matrix.transpose_prodFwd`), and products of unitary or orthogonal matrices are
unitary or orthogonal (`Matrix.prodFwd_mem_unitaryGroup`, `Matrix.prodFwd_mem_orthogonalGroup`).
-/

section Monoid

variable {M : Type*} [Monoid M]

/-- `P (r-1) * ⋯ * P 1 * P 0`: the product of the first `r` terms of a sequence, each new one
multiplying on the left. -/
def prodRev (P : ℕ → M) : ℕ → M
  | 0 => 1
  | r + 1 => P r * prodRev P r

/-- `P 0 * P 1 * ⋯ * P (r-1)`: the product of the first `r` terms of a sequence, each new one
multiplying on the right. -/
def prodFwd (P : ℕ → M) : ℕ → M
  | 0 => 1
  | r + 1 => prodFwd P r * P r

/-- The empty product is the identity. -/
@[simp]
theorem prodRev_zero (P : ℕ → M) : prodRev P 0 = 1 := rfl

/-- One more factor on the left. -/
theorem prodRev_succ (P : ℕ → M) (r : ℕ) : prodRev P (r + 1) = P r * prodRev P r :=
  rfl

/-- The empty product is the identity. -/
@[simp]
theorem prodFwd_zero (P : ℕ → M) : prodFwd P 0 = 1 := rfl

/-- One more factor on the right. -/
theorem prodFwd_succ (P : ℕ → M) (r : ℕ) : prodFwd P (r + 1) = prodFwd P r * P r :=
  rfl

/-- A reverse product only reads its first `r` factors. -/
theorem prodRev_congr {f f' : ℕ → M} {r : ℕ} (h : ∀ k < r, f k = f' k) :
    prodRev f r = prodRev f' r := by
  induction r with
  | zero => rfl
  | succ r ih => rw [prodRev_succ, prodRev_succ, ih fun k hk => h k (by omega), h r (by omega)]

/-- A forward product only reads its first `r` factors. -/
theorem prodFwd_congr {f f' : ℕ → M} {r : ℕ} (h : ∀ k < r, f k = f' k) :
    prodFwd f r = prodFwd f' r := by
  induction r with
  | zero => rfl
  | succ r ih => rw [prodFwd_succ, prodFwd_succ, ih fun k hk => h k (by omega), h r (by omega)]

/-- Peeling off the first factor of a reverse product, on the right. -/
theorem prodRev_succ' (f : ℕ → M) (r : ℕ) :
    prodRev f (r + 1) = prodRev (fun k => f (k + 1)) r * f 0 := by
  induction r with
  | zero => simp [prodRev_succ]
  | succ r ih => rw [prodRev_succ, ih, prodRev_succ, mul_assoc]

/-- Peeling off the first factor of a forward product, on the left. -/
theorem prodFwd_succ' (f : ℕ → M) (r : ℕ) :
    prodFwd f (r + 1) = f 0 * prodFwd (fun k => f (k + 1)) r := by
  induction r with
  | zero => simp [prodFwd_succ]
  | succ r ih => rw [prodFwd_succ, ih, prodFwd_succ, mul_assoc]

/-- A reverse product is the product of the reversed list of its factors. -/
theorem prodRev_eq_prod_ofFn (P : ℕ → M) (r : ℕ) :
    prodRev P r = (List.ofFn fun j : Fin r => P j).reverse.prod := by
  induction r with
  | zero => simp
  | succ r ih => simp [prodRev_succ, ih, List.ofFn_succ', -List.ofFn_succ]

/-- A forward product is the product of the list of its factors. -/
theorem prodFwd_eq_prod_ofFn (P : ℕ → M) (r : ℕ) :
    prodFwd P r = (List.ofFn fun j : Fin r => P j).prod := by
  induction r with
  | zero => simp
  | succ r ih => simp [prodFwd_succ, ih, List.ofFn_succ', -List.ofFn_succ]

/-- The product over a range `b, b + 1, …, b + n - 1` is a forward product. -/
theorem prod_map_range'_eq_prodFwd (P : ℕ → M) (b n : ℕ) :
    ((List.range' b n).map P).prod = prodFwd (fun k => P (b + k)) n := by
  induction n generalizing b with
  | zero => simp
  | succ n ih =>
    rw [List.range'_succ, List.map_cons, List.prod_cons, ih, prodFwd_succ', add_zero]
    simp only [Nat.add_assoc, Nat.add_comm 1]

/-- A monoid homomorphism maps a reverse product factorwise. -/
theorem map_prodRev {N F : Type*} [Monoid N] [FunLike F M N] [MonoidHomClass F M N] (φ : F)
    (P : ℕ → M) (r : ℕ) : φ (prodRev P r) = prodRev (fun k => φ (P k)) r := by
  induction r with
  | zero => simp
  | succ r ih => rw [prodRev_succ, map_mul, ih, prodRev_succ]

/-- A monoid homomorphism maps a forward product factorwise. -/
theorem map_prodFwd {N F : Type*} [Monoid N] [FunLike F M N] [MonoidHomClass F M N] (φ : F)
    (P : ℕ → M) (r : ℕ) : φ (prodFwd P r) = prodFwd (fun k => φ (P k)) r := by
  induction r with
  | zero => simp
  | succ r ih => rw [prodFwd_succ, map_mul, ih, prodFwd_succ]

/-- A reverse product commutes with an element commuting with its factors. -/
theorem commute_prodRev {f : ℕ → M} {y : M} {r : ℕ} (h : ∀ k < r, Commute (f k) y) :
    Commute (prodRev f r) y := by
  induction r with
  | zero => exact Commute.one_left y
  | succ r ih =>
    rw [prodRev_succ]
    exact (h r (by omega)).mul_left (ih fun k hk => h k (by omega))

/-- A forward product commutes with an element commuting with its factors. -/
theorem commute_prodFwd {f : ℕ → M} {y : M} {r : ℕ} (h : ∀ k < r, Commute (f k) y) :
    Commute (prodFwd f r) y := by
  induction r with
  | zero => exact Commute.one_left y
  | succ r ih =>
    rw [prodFwd_succ]
    exact (ih fun k hk => h k (by omega)).mul_left (h r (by omega))

/-- A reverse product of invertible elements is invertible. -/
theorem isUnit_prodRev {f : ℕ → M} {r : ℕ} (h : ∀ k < r, IsUnit (f k)) :
    IsUnit (prodRev f r) := by
  induction r with
  | zero => exact isUnit_one
  | succ r ih =>
    rw [prodRev_succ]
    exact (h r (by omega)).mul (ih fun k hk => h k (by omega))

/-- A forward product of invertible elements is invertible. -/
theorem isUnit_prodFwd {f : ℕ → M} {r : ℕ} (h : ∀ k < r, IsUnit (f k)) :
    IsUnit (prodFwd f r) := by
  induction r with
  | zero => exact isUnit_one
  | succ r ih =>
    rw [prodFwd_succ]
    exact (ih fun k hk => h k (by omega)).mul (h r (by omega))

/-- For involutions, the reverse product inverts the forward product. -/
theorem prodRev_mul_prodFwd {P : ℕ → M} {r : ℕ} (hP : ∀ k < r, P k * P k = 1) :
    prodRev P r * prodFwd P r = 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [prodRev_succ, prodFwd_succ, mul_assoc, ← mul_assoc (prodRev P r),
      ih fun k hk => hP k (by omega), one_mul, hP r (by omega)]

/-- For involutions, the forward product inverts the reverse product. -/
theorem prodFwd_mul_prodRev {P : ℕ → M} {r : ℕ} (hP : ∀ k < r, P k * P k = 1) :
    prodFwd P r * prodRev P r = 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [prodFwd_succ, prodRev_succ, mul_assoc, ← mul_assoc (P r), hP r (by omega),
      one_mul, ih fun k hk => hP k (by omega)]

/-- A forward product of pairwise commuting involutions is an involution. -/
theorem prodFwd_mul_self {f : ℕ → M} {r : ℕ}
    (hc : ∀ k l, k < l → l < r → Commute (f k) (f l)) (hf : ∀ k < r, f k * f k = 1) :
    prodFwd f r * prodFwd f r = 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hP : Commute (prodFwd f r) (f r) :=
      commute_prodFwd fun k hk => hc k r hk (lt_add_one r)
    rw [prodFwd_succ, mul_assoc, ← mul_assoc (f r), ← hP.eq, mul_assoc,
      hf r (lt_add_one r), mul_one, ih (fun k l hkl hl => hc k l hkl (by omega))
        fun k hk => hf k (by omega)]

/-- A reverse product of members of a submonoid is a member. -/
theorem prodRev_mem {S : Submonoid M} {P : ℕ → M} {r : ℕ} (hP : ∀ k < r, P k ∈ S) :
    prodRev P r ∈ S := by
  induction r with
  | zero => exact S.one_mem
  | succ r ih => exact S.mul_mem (hP r (by omega)) (ih fun k hk => hP k (by omega))

/-- A forward product of members of a submonoid is a member. -/
theorem prodFwd_mem {S : Submonoid M} {P : ℕ → M} {r : ℕ} (hP : ∀ k < r, P k ∈ S) :
    prodFwd P r ∈ S := by
  induction r with
  | zero => exact S.one_mem
  | succ r ih => exact S.mul_mem (ih fun k hk => hP k (by omega)) (hP r (by omega))

end Monoid

section Ring

variable {R : Type*} [Ring R]

/-- A forward product of factors with pairwise disjoint supports is the identity plus the sum of
their departures from it: `∏ (1 + E_k) = 1 + ∑ E_k` when `E_k E_l = 0` for `k < l`. -/
theorem prodFwd_eq_one_add_sum_sub_one {f : ℕ → R} {m : ℕ}
    (h : ∀ k l, k < l → l < m → (f k - 1) * (f l - 1) = 0) :
    prodFwd f m = 1 + ∑ k ∈ Finset.range m, (f k - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hS : (∑ k ∈ Finset.range m, (f k - 1)) * (f m - 1) = 0 := by
      rw [Finset.sum_mul]
      exact Finset.sum_eq_zero fun k hk => h k m (Finset.mem_range.1 hk) (lt_add_one m)
    rw [prodFwd_succ, ih fun k l hkl hl => h k l hkl (by omega), Finset.sum_range_succ]
    calc (1 + ∑ k ∈ Finset.range m, (f k - 1)) * f m
        = (1 + ∑ k ∈ Finset.range m, (f k - 1)) * (1 + (f m - 1)) := by congr 1; abel
      _ = _ := by
        rw [mul_add, mul_one, add_mul (1 : R), one_mul, hS]
        abel

/-- Two elements whose departures from the identity annihilate each other in both orders
commute: both products are `a + b − 1`. -/
theorem commute_of_sub_one_mul_sub_one {a b : R} (h₁ : (a - 1) * (b - 1) = 0)
    (h₂ : (b - 1) * (a - 1) = 0) : Commute a b := by
  calc a * b = (a - 1) * (b - 1) + a + b - 1 := by noncomm_ring
    _ = (b - 1) * (a - 1) + a + b - 1 := by rw [h₁, h₂]
    _ = b * a := by noncomm_ring

end Ring

namespace Matrix

variable {ι α : Type*} [Fintype ι] [DecidableEq ι]

/-- The determinant of a reverse product is the product of the determinants. -/
theorem det_prodRev [CommRing α] (P : ℕ → Matrix ι ι α) (r : ℕ) :
    (prodRev P r).det = ∏ k ∈ Finset.range r, (P k).det := by
  induction r with
  | zero => simp
  | succ r ih => rw [prodRev_succ, det_mul, ih, Finset.prod_range_succ, mul_comm]

/-- The determinant of a forward product is the product of the determinants. -/
theorem det_prodFwd [CommRing α] (P : ℕ → Matrix ι ι α) (r : ℕ) :
    (prodFwd P r).det = ∏ k ∈ Finset.range r, (P k).det := by
  induction r with
  | zero => simp
  | succ r ih => rw [prodFwd_succ, det_mul, ih, Finset.prod_range_succ]

/-- The transpose of `prodRev P r` is `prodFwd Pᵀ r`. -/
theorem transpose_prodRev [CommSemiring α] (P : ℕ → Matrix ι ι α) (r : ℕ) :
    (prodRev P r)ᵀ = prodFwd (fun k => (P k)ᵀ) r := by
  induction r with
  | zero => simp
  | succ r ih => rw [prodRev_succ, transpose_mul, ih, prodFwd_succ]

/-- The transpose of `prodFwd P r` is `prodRev Pᵀ r`. -/
theorem transpose_prodFwd [CommSemiring α] (P : ℕ → Matrix ι ι α) (r : ℕ) :
    (prodFwd P r)ᵀ = prodRev (fun k => (P k)ᵀ) r := by
  induction r with
  | zero => simp
  | succ r ih => rw [prodFwd_succ, transpose_mul, ih, prodRev_succ]

/-- The product of unitary matrices is unitary. -/
theorem prodRev_mem_unitaryGroup [CommRing α] [StarRing α] {P : ℕ → Matrix ι ι α} {r : ℕ}
    (hP : ∀ k < r, P k ∈ Matrix.unitaryGroup ι α) : prodRev P r ∈ Matrix.unitaryGroup ι α :=
  prodRev_mem hP

/-- The product of unitary matrices is unitary. -/
theorem prodFwd_mem_unitaryGroup [CommRing α] [StarRing α] {P : ℕ → Matrix ι ι α} {r : ℕ}
    (hP : ∀ k < r, P k ∈ Matrix.unitaryGroup ι α) : prodFwd P r ∈ Matrix.unitaryGroup ι α :=
  prodFwd_mem hP

/-- The product of orthogonal matrices is orthogonal. -/
theorem prodRev_mem_orthogonalGroup [CommRing α] {P : ℕ → Matrix ι ι α} {r : ℕ}
    (hP : ∀ k < r, P k ∈ Matrix.orthogonalGroup ι α) :
    prodRev P r ∈ Matrix.orthogonalGroup ι α :=
  prodRev_mem hP

/-- The product of orthogonal matrices is orthogonal. -/
theorem prodFwd_mem_orthogonalGroup [CommRing α] {P : ℕ → Matrix ι ι α} {r : ℕ}
    (hP : ∀ k < r, P k ∈ Matrix.orthogonalGroup ι α) :
    prodFwd P r ∈ Matrix.orthogonalGroup ι α :=
  prodFwd_mem hP

end Matrix
