/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

Let $P_0, P_1, \dots$ be a sequence in a monoid. This module defines the products of its first $r$
terms in the two orders in which a sequence of transformations accumulates:
$$\operatorname{prodRev}(P, r) = P_{r-1} \cdots P_1 P_0, \qquad \operatorname{prodFwd}(P, r) = P_0
  P_1 \cdots P_{r-1}.$$
In the reverse product each new factor multiplies on the left. It is the accumulated transformation
$Q_r$ of a recursion $x_{k+1} = P_k x_k$, as in the backward error analysis of a sequence of
Householder or Givens transformations (Lemma 19.3 of [higham2002accuracy]). In the forward product
each new factor multiplies on the right. It is the orthogonal factor $Q = Q_1 \cdots Q_r$ of a
factorization built one reflector at a time (the WY representations of §5.1.6–5.1.7 of
[golub2013matrix]), or the product of a sweep of plane rotations. The subproducts of the factors
with even and with odd index are the two halves of the odd–even reordering of a product whose
far-apart factors commute (§12.2.10 of [golub2013matrix]).

The products obey the usual monoid algebra, in both orders: they depend only on their first $r$
factors, they commute with an element that commutes with every factor, they are invertible when
every factor is, they stay in a submonoid that contains every factor, and a monoid homomorphism maps
them factor by factor. For involutions the two orders are inverse to each other. In a ring, if the
departures $E_k = P_k - 1$ from the identity satisfy $E_k E_l = 0$ for $k < l$, then
$\operatorname{prodFwd}(P, r) = 1 + \sum_{k < r} E_k$. For matrices, the determinant of a product is
the product of the determinants, transposition exchanges the two orders, and products of unitary or
orthogonal matrices are unitary or orthogonal.

## Main definitions

* `prodRev`: the reverse product $P_{r-1} \cdots P_1 P_0$.
* `prodFwd`: the forward product $P_0 P_1 \cdots P_{r-1}$.
* `prodFwdEven`, `prodFwdOdd`: the forward products of the factors with even and with odd index.

## Main results

* `prodFwd_eq_prod_ofFn`, `prodRev_eq_prod_ofFn`: the forward and the reverse product are the
  products of the list $(P_0, \dots, P_{r-1})$ and of its reverse.
* `prod_map_range'_eq_prodFwd`: the product of the list $(P_b, P_{b+1}, \dots, P_{b+n-1})$ is a
  forward product.
* `prodFwd_mul_prodRev`, `prodRev_mul_prodFwd`: for involutions, the two products are inverse to
  each other.
* `prodFwd_eq_one_add_sum_sub_one`: if $(P_k - 1)(P_l - 1) = 0$ for $k < l$, the forward product is
  $1 + \sum_k (P_k - 1)$.
* `commute_of_sub_one_mul_sub_one`: two ring elements whose departures from $1$ annihilate each
  other in both orders commute.
* `Matrix.det_prodFwd`, `Matrix.det_prodRev`: the determinant of a product is the product of the
  determinants.
* `Matrix.transpose_prodFwd`, `Matrix.transpose_prodRev`: the transpose of a product in one order is
  the product of the transposes in the other order.
* `Matrix.prodFwd_mem_unitaryGroup`, `Matrix.prodFwd_mem_orthogonalGroup`: products of unitary or
  orthogonal matrices are unitary or orthogonal.

## Implementation notes

* Both products are recursions on $r$, so statements about them are proved by induction on $r$
  without casts between `Fin` types. The list forms connect them to `List.prod` of
  `List.ofFn fun j : Fin r => P j`, of its reverse, and of `(List.range' b n).map P`.
* Every algebraic lemma is stated for both orders.
* The declarations of the monoid and ring part are in the root namespace.
-/

section Monoid

variable {M : Type*} [Monoid M]

/-- The **reverse product** of the first $r$ terms of a sequence $P$ in a monoid:
$$\operatorname{prodRev}(P, r) = P_{r-1} \cdots P_1 P_0,$$
in which each new factor multiplies on the left. It is defined by
$\operatorname{prodRev}(P, 0) = 1$ and $\operatorname{prodRev}(P, r + 1) = P_r
\operatorname{prodRev}(P, r)$. -/
def prodRev (P : ℕ → M) : ℕ → M
  | 0 => 1
  | r + 1 => P r * prodRev P r

/-- The **forward product** of the first $r$ terms of a sequence $P$ in a monoid:
$$\operatorname{prodFwd}(P, r) = P_0 P_1 \cdots P_{r-1},$$
in which each new factor multiplies on the right. It is defined by
$\operatorname{prodFwd}(P, 0) = 1$ and $\operatorname{prodFwd}(P, r + 1) =
\operatorname{prodFwd}(P, r) P_r$. -/
def prodFwd (P : ℕ → M) : ℕ → M
  | 0 => 1
  | r + 1 => prodFwd P r * P r

/-- The forward product of the factors with an even index below $m$, in increasing order:
$$\operatorname{prodFwdEven}(g, m) = \prod_{k < m, \ k \text{ even}} g_k = g_0 g_2 g_4 \cdots.$$

This is the product $H_o = G_1 G_3 \cdots$ of §12.2.10 of [golub2013matrix], whose indices start
at $1$. The definition is the forward product of the sequence that is $g_k$ at even $k$ and $1$
at odd $k$. -/
def prodFwdEven (g : ℕ → M) (m : ℕ) : M :=
  prodFwd (fun k => if Even k then g k else 1) m

/-- The forward product of the factors with an odd index below $m$, in increasing order:
$$\operatorname{prodFwdOdd}(g, m) = \prod_{k < m, \ k \text{ odd}} g_k = g_1 g_3 g_5 \cdots.$$

This is the product $H_e = G_2 G_4 \cdots$ of §12.2.10 of [golub2013matrix], whose indices start
at $1$. The definition is the forward product of the sequence that is $g_k$ at odd $k$ and $1$
at even $k$. -/
def prodFwdOdd (g : ℕ → M) (m : ℕ) : M :=
  prodFwd (fun k => if Odd k then g k else 1) m

/-- The reverse product of no terms is the identity: $\operatorname{prodRev}(P, 0) = 1$. -/
@[simp]
theorem prodRev_zero (P : ℕ → M) : prodRev P 0 = 1 := rfl

/-- The reverse product of $r + 1$ terms has one more factor on the left: $\operatorname{prodRev}(P,
r + 1) = P_r \operatorname{prodRev}(P, r)$. -/
theorem prodRev_succ (P : ℕ → M) (r : ℕ) : prodRev P (r + 1) = P r * prodRev P r :=
  rfl

/-- The forward product of no terms is the identity: $\operatorname{prodFwd}(P, 0) = 1$. -/
@[simp]
theorem prodFwd_zero (P : ℕ → M) : prodFwd P 0 = 1 := rfl

/-- The forward product of $r + 1$ terms has one more factor on the right:
$\operatorname{prodFwd}(P, r + 1) = \operatorname{prodFwd}(P, r) P_r$. -/
theorem prodFwd_succ (P : ℕ → M) (r : ℕ) : prodFwd P (r + 1) = prodFwd P r * P r :=
  rfl

/-- A reverse product depends only on its first $r$ factors: if $f_k = f'_k$ for all $k < r$, then
$\operatorname{prodRev}(f, r) = \operatorname{prodRev}(f', r)$. -/
theorem prodRev_congr {f f' : ℕ → M} {r : ℕ} (h : ∀ k < r, f k = f' k) :
    prodRev f r = prodRev f' r := by
  induction r with
  | zero => rfl
  | succ r ih => rw [prodRev_succ, prodRev_succ, ih fun k hk => h k (by omega), h r (by omega)]

/-- A forward product depends only on its first $r$ factors: if $f_k = f'_k$ for all $k < r$, then
$\operatorname{prodFwd}(f, r) = \operatorname{prodFwd}(f', r)$. -/
theorem prodFwd_congr {f f' : ℕ → M} {r : ℕ} (h : ∀ k < r, f k = f' k) :
    prodFwd f r = prodFwd f' r := by
  induction r with
  | zero => rfl
  | succ r ih => rw [prodFwd_succ, prodFwd_succ, ih fun k hk => h k (by omega), h r (by omega)]

/-- The first factor of a reverse product splits off on the right: $\operatorname{prodRev}(f,
r + 1) = \operatorname{prodRev}(k \mapsto f_{k+1}, r) \, f_0$. -/
theorem prodRev_succ' (f : ℕ → M) (r : ℕ) :
    prodRev f (r + 1) = prodRev (fun k => f (k + 1)) r * f 0 := by
  induction r with
  | zero => simp [prodRev_succ]
  | succ r ih => rw [prodRev_succ, ih, prodRev_succ, mul_assoc]

/-- The first factor of a forward product splits off on the left: $\operatorname{prodFwd}(f,
r + 1) = f_0 \operatorname{prodFwd}(k \mapsto f_{k+1}, r)$. -/
theorem prodFwd_succ' (f : ℕ → M) (r : ℕ) :
    prodFwd f (r + 1) = f 0 * prodFwd (fun k => f (k + 1)) r := by
  induction r with
  | zero => simp [prodFwd_succ]
  | succ r ih => rw [prodFwd_succ, ih, prodFwd_succ, mul_assoc]

/-- A reverse product is the product of the reversed list $(P_{r-1}, \dots, P_1, P_0)$. -/
theorem prodRev_eq_prod_ofFn (P : ℕ → M) (r : ℕ) :
    prodRev P r = (List.ofFn fun j : Fin r => P j).reverse.prod := by
  induction r with
  | zero => simp
  | succ r ih => simp [prodRev_succ, ih, List.ofFn_succ', -List.ofFn_succ]

/-- A forward product is the product of the list $(P_0, P_1, \dots, P_{r-1})$. -/
theorem prodFwd_eq_prod_ofFn (P : ℕ → M) (r : ℕ) :
    prodFwd P r = (List.ofFn fun j : Fin r => P j).prod := by
  induction r with
  | zero => simp
  | succ r ih => simp [prodFwd_succ, ih, List.ofFn_succ', -List.ofFn_succ]

/-- The product of the list $(P_b, P_{b+1}, \dots, P_{b+n-1})$ is the forward product
$\operatorname{prodFwd}(k \mapsto P_{b+k}, n)$. -/
theorem prod_map_range'_eq_prodFwd (P : ℕ → M) (b n : ℕ) :
    ((List.range' b n).map P).prod = prodFwd (fun k => P (b + k)) n := by
  induction n generalizing b with
  | zero => simp
  | succ n ih =>
    rw [List.range'_succ, List.map_cons, List.prod_cons, ih, prodFwd_succ', add_zero]
    simp only [Nat.add_assoc, Nat.add_comm 1]

/-- A monoid homomorphism $\varphi$ maps a reverse product factor by factor:
$\varphi(\operatorname{prodRev}(P, r)) = \operatorname{prodRev}(k \mapsto \varphi(P_k), r)$. -/
theorem map_prodRev {N F : Type*} [Monoid N] [FunLike F M N] [MonoidHomClass F M N] (φ : F)
    (P : ℕ → M) (r : ℕ) : φ (prodRev P r) = prodRev (fun k => φ (P k)) r := by
  induction r with
  | zero => simp
  | succ r ih => rw [prodRev_succ, map_mul, ih, prodRev_succ]

/-- A monoid homomorphism $\varphi$ maps a forward product factor by factor:
$\varphi(\operatorname{prodFwd}(P, r)) = \operatorname{prodFwd}(k \mapsto \varphi(P_k), r)$. -/
theorem map_prodFwd {N F : Type*} [Monoid N] [FunLike F M N] [MonoidHomClass F M N] (φ : F)
    (P : ℕ → M) (r : ℕ) : φ (prodFwd P r) = prodFwd (fun k => φ (P k)) r := by
  induction r with
  | zero => simp
  | succ r ih => rw [prodFwd_succ, map_mul, ih, prodFwd_succ]

/-- If $y$ commutes with $f_k$ for every $k < r$, then $y$ commutes with
$\operatorname{prodRev}(f, r)$. -/
theorem commute_prodRev {f : ℕ → M} {y : M} {r : ℕ} (h : ∀ k < r, Commute (f k) y) :
    Commute (prodRev f r) y := by
  induction r with
  | zero => exact Commute.one_left y
  | succ r ih =>
    rw [prodRev_succ]
    exact (h r (by omega)).mul_left (ih fun k hk => h k (by omega))

/-- If $y$ commutes with $f_k$ for every $k < r$, then $y$ commutes with
$\operatorname{prodFwd}(f, r)$. -/
theorem commute_prodFwd {f : ℕ → M} {y : M} {r : ℕ} (h : ∀ k < r, Commute (f k) y) :
    Commute (prodFwd f r) y := by
  induction r with
  | zero => exact Commute.one_left y
  | succ r ih =>
    rw [prodFwd_succ]
    exact (ih fun k hk => h k (by omega)).mul_left (h r (by omega))

/-- If $f_k$ is invertible for every $k < r$, then $\operatorname{prodRev}(f, r)$ is invertible. -/
theorem isUnit_prodRev {f : ℕ → M} {r : ℕ} (h : ∀ k < r, IsUnit (f k)) :
    IsUnit (prodRev f r) := by
  induction r with
  | zero => exact isUnit_one
  | succ r ih =>
    rw [prodRev_succ]
    exact (h r (by omega)).mul (ih fun k hk => h k (by omega))

/-- If $f_k$ is invertible for every $k < r$, then $\operatorname{prodFwd}(f, r)$ is invertible. -/
theorem isUnit_prodFwd {f : ℕ → M} {r : ℕ} (h : ∀ k < r, IsUnit (f k)) :
    IsUnit (prodFwd f r) := by
  induction r with
  | zero => exact isUnit_one
  | succ r ih =>
    rw [prodFwd_succ]
    exact (ih fun k hk => h k (by omega)).mul (h r (by omega))

/-- For involutions the reverse product is a left inverse of the forward product: if $P_k P_k = 1$
for every $k < r$, then $\operatorname{prodRev}(P, r) \operatorname{prodFwd}(P, r) = 1$. -/
theorem prodRev_mul_prodFwd {P : ℕ → M} {r : ℕ} (hP : ∀ k < r, P k * P k = 1) :
    prodRev P r * prodFwd P r = 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [prodRev_succ, prodFwd_succ, mul_assoc, ← mul_assoc (prodRev P r),
      ih fun k hk => hP k (by omega), one_mul, hP r (by omega)]

/-- For involutions the forward product is a left inverse of the reverse product: if $P_k P_k = 1$
for every $k < r$, then $\operatorname{prodFwd}(P, r) \operatorname{prodRev}(P, r) = 1$. -/
theorem prodFwd_mul_prodRev {P : ℕ → M} {r : ℕ} (hP : ∀ k < r, P k * P k = 1) :
    prodFwd P r * prodRev P r = 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [prodFwd_succ, prodRev_succ, mul_assoc, ← mul_assoc (P r), hP r (by omega),
      one_mul, ih fun k hk => hP k (by omega)]

/-- A forward product of pairwise commuting involutions is an involution: if $f_k$ and $f_l$ commute
for all $k < l < r$ and $f_k f_k = 1$ for all $k < r$, then
$\operatorname{prodFwd}(f, r)^2 = 1$. -/
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

/-- If $P_k$ belongs to a submonoid $S$ for every $k < r$, then
$\operatorname{prodRev}(P, r) \in S$. -/
theorem prodRev_mem {S : Submonoid M} {P : ℕ → M} {r : ℕ} (hP : ∀ k < r, P k ∈ S) :
    prodRev P r ∈ S := by
  induction r with
  | zero => exact S.one_mem
  | succ r ih => exact S.mul_mem (hP r (by omega)) (ih fun k hk => hP k (by omega))

/-- If $P_k$ belongs to a submonoid $S$ for every $k < r$, then
$\operatorname{prodFwd}(P, r) \in S$. -/
theorem prodFwd_mem {S : Submonoid M} {P : ℕ → M} {r : ℕ} (hP : ∀ k < r, P k ∈ S) :
    prodFwd P r ∈ S := by
  induction r with
  | zero => exact S.one_mem
  | succ r ih => exact S.mul_mem (ih fun k hk => hP k (by omega)) (hP r (by omega))

end Monoid

section Ring

variable {R : Type*} [Ring R]

/-- Let $R$ be a ring and $f_0, f_1, \dots \in R$. If the departures $E_k = f_k - 1$ from the
identity satisfy $E_k E_l = 0$ for all $k < l < m$, then the forward product is the identity
plus the sum of the departures:
$$\operatorname{prodFwd}(f, m) = \prod_{k < m} (1 + E_k) = 1 + \sum_{k < m} E_k.$$

For matrices, the condition holds when the factors differ from the identity on pairwise disjoint
sets of rows and columns. -/
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

/-- Let $R$ be a ring and $a, b \in R$. If $(a - 1)(b - 1) = 0$ and $(b - 1)(a - 1) = 0$, then $a$
and $b$ commute: both products $a b$ and $b a$ equal $a + b - 1$. -/
theorem commute_of_sub_one_mul_sub_one {a b : R} (h₁ : (a - 1) * (b - 1) = 0)
    (h₂ : (b - 1) * (a - 1) = 0) : Commute a b := by
  calc a * b = (a - 1) * (b - 1) + a + b - 1 := by noncomm_ring
    _ = (b - 1) * (a - 1) + a + b - 1 := by rw [h₁, h₂]
    _ = b * a := by noncomm_ring

end Ring

namespace Matrix

variable {ι α : Type*} [Fintype ι] [DecidableEq ι]

/-- For square matrices over a commutative ring, the determinant of a reverse product is the product
of the determinants: $\det \operatorname{prodRev}(P, r) = \prod_{k < r} \det P_k$. -/
theorem det_prodRev [CommRing α] (P : ℕ → Matrix ι ι α) (r : ℕ) :
    (prodRev P r).det = ∏ k ∈ Finset.range r, (P k).det := by
  induction r with
  | zero => simp
  | succ r ih => rw [prodRev_succ, det_mul, ih, Finset.prod_range_succ, mul_comm]

/-- For square matrices over a commutative ring, the determinant of a forward product is the product
of the determinants: $\det \operatorname{prodFwd}(P, r) = \prod_{k < r} \det P_k$. -/
theorem det_prodFwd [CommRing α] (P : ℕ → Matrix ι ι α) (r : ℕ) :
    (prodFwd P r).det = ∏ k ∈ Finset.range r, (P k).det := by
  induction r with
  | zero => simp
  | succ r ih => rw [prodFwd_succ, det_mul, ih, Finset.prod_range_succ]

/-- For square matrices over a commutative semiring, $\operatorname{prodRev}(P, r)^T =
\operatorname{prodFwd}(k \mapsto P_k^T, r)$. -/
theorem transpose_prodRev [CommSemiring α] (P : ℕ → Matrix ι ι α) (r : ℕ) :
    (prodRev P r)ᵀ = prodFwd (fun k => (P k)ᵀ) r := by
  induction r with
  | zero => simp
  | succ r ih => rw [prodRev_succ, transpose_mul, ih, prodFwd_succ]

/-- For square matrices over a commutative semiring, $\operatorname{prodFwd}(P, r)^T =
\operatorname{prodRev}(k \mapsto P_k^T, r)$. -/
theorem transpose_prodFwd [CommSemiring α] (P : ℕ → Matrix ι ι α) (r : ℕ) :
    (prodFwd P r)ᵀ = prodRev (fun k => (P k)ᵀ) r := by
  induction r with
  | zero => simp
  | succ r ih => rw [prodFwd_succ, transpose_mul, ih, prodRev_succ]

/-- Let $\alpha$ be a commutative ring with a star operation and let $P_0, P_1, \dots \in
\alpha^{\iota \times \iota}$, with $\iota$ finite. If $P_k$ is unitary for every $k < r$, then
the reverse product
$$\operatorname{prodRev}(P, r) = P_{r-1} \cdots P_1 P_0$$
is unitary. -/
theorem prodRev_mem_unitaryGroup [CommRing α] [StarRing α] {P : ℕ → Matrix ι ι α} {r : ℕ}
    (hP : ∀ k < r, P k ∈ Matrix.unitaryGroup ι α) : prodRev P r ∈ Matrix.unitaryGroup ι α :=
  prodRev_mem hP

/-- Let $\alpha$ be a commutative ring with a star operation and let $P_0, P_1, \dots \in
\alpha^{\iota \times \iota}$, with $\iota$ finite. If $P_k$ is unitary for every $k < r$, then
the forward product
$$\operatorname{prodFwd}(P, r) = P_0 P_1 \cdots P_{r-1}$$
is unitary. -/
theorem prodFwd_mem_unitaryGroup [CommRing α] [StarRing α] {P : ℕ → Matrix ι ι α} {r : ℕ}
    (hP : ∀ k < r, P k ∈ Matrix.unitaryGroup ι α) : prodFwd P r ∈ Matrix.unitaryGroup ι α :=
  prodFwd_mem hP

/-- Let $\alpha$ be a commutative ring and let $P_0, P_1, \dots \in \alpha^{\iota \times \iota}$,
with $\iota$ finite. If $P_k$ is orthogonal for every $k < r$, then the reverse product
$$\operatorname{prodRev}(P, r) = P_{r-1} \cdots P_1 P_0$$
is orthogonal. -/
theorem prodRev_mem_orthogonalGroup [CommRing α] {P : ℕ → Matrix ι ι α} {r : ℕ}
    (hP : ∀ k < r, P k ∈ Matrix.orthogonalGroup ι α) :
    prodRev P r ∈ Matrix.orthogonalGroup ι α :=
  prodRev_mem hP

/-- Let $\alpha$ be a commutative ring and let $P_0, P_1, \dots \in \alpha^{\iota \times \iota}$,
with $\iota$ finite. If $P_k$ is orthogonal for every $k < r$, then the forward product
$$\operatorname{prodFwd}(P, r) = P_0 P_1 \cdots P_{r-1}$$
is orthogonal. -/
theorem prodFwd_mem_orthogonalGroup [CommRing α] {P : ℕ → Matrix ι ι α} {r : ℕ}
    (hP : ∀ k < r, P k ∈ Matrix.orthogonalGroup ι α) :
    prodFwd P r ∈ Matrix.orthogonalGroup ι α :=
  prodFwd_mem hP

end Matrix
