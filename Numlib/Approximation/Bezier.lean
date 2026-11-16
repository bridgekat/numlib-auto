/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.RingTheory.Polynomial.Bernstein
import Numlib.Approximation.Chebyshev

/-!
# Bernstein polynomials and Bézier curves

This file studies the Bernstein polynomials $b_{n,k}(X) = \binom{n}{k} X^k (1 - X)^{n-k}$ and the
Bézier curves built from them. It proves the recursion $b_{n+1,k+1} = (1 - X)\, b_{n,k+1} + X\,
b_{n,k}$, the degree bound $\deg b_{n,k} \le n$, the linear independence of
$b_{n,0}, \dots, b_{n,n}$ over any field of characteristic zero, and the fact that they form a basis
of the polynomials of degree at most $n$ on any infinite subset of $\mathbb{R}$. The Bézier curve of
the control points $P_0, \dots, P_n$ in a real vector space $E$ is
$$B_n(P; t) = \sum_{k=0}^n b_{n,k}(t)\, P_k.$$
De Casteljau's algorithm evaluates it, and it has the endpoint, reversal, convex-hull and
affine-equivariance properties. The material follows §8.7.1 of [quarteroni2000numerical] and
chapters 4–5 of Farin, *Curves and Surfaces for CAGD*.

Nothing here needs a knot sequence, so this module is separate from the B-spline theory of
`Numlib.Approximation.BSpline`: the Bernstein basis is the B-spline basis on the two knots $0$ and
$1$, each of multiplicity $n + 1$.

## Main definitions

* `bernsteinPolynomial.toPolyLE`: the Bernstein polynomial $b_{n,k}$ as an element of the space of
  polynomial functions of degree at most $n$ on a set $X \subseteq \mathbb{R}$.
* `Bezier.curve`: the Bézier curve $B_n(P; t)$ of the control points $P_0, \dots, P_n$.
* `Bezier.casteljauStep`, `Bezier.casteljau`: one step of de Casteljau's construction, and de
  Casteljau's algorithm.

## Main results

* `bernsteinPolynomial.succ_succ`, `bernsteinPolynomial.succ_zero`: the recursion of the Bernstein
  polynomials.
* `bernsteinPolynomial.degree_le`: $b_{n,k}$ has degree at most $n$.
* `bernsteinPolynomial.linearIndependent'`: $b_{n,0}, \dots, b_{n,n}$ are linearly independent over
  any field of characteristic zero.
* `bernsteinPolynomial.exists_basis_polyLE`: on an infinite set $X \subseteq \mathbb{R}$, the
  Bernstein polynomials of degree $n$ form a basis of the polynomial functions of degree at most
  $n$.
* `Bezier.curve_succ`: the Bézier recursion $B_{n+1}(P_0, \dots, P_{n+1}) = (1 - t) B_n(P_0, \dots,
  P_n) + t B_n(P_1, \dots, P_{n+1})$.
* `Bezier.casteljau_eq_curve`: de Casteljau's algorithm evaluates the Bézier curve.
* `Bezier.curve_zero`, `Bezier.curve_one`, `Bezier.curve_rev`, `Bezier.curve_mem_convexHull`,
  `Bezier.curve_affine`: the curve starts at $P_0$ and ends at $P_n$, reversing the control points
  reverses the curve, the curve for $t \in [0, 1]$ lies in the convex hull of the control points,
  and the curve commutes with affine maps.

## Implementation notes

* Mathlib has the polynomials `bernsteinPolynomial R n ν : R[X]` with
  `bernsteinPolynomial.eval_at_0`, `bernsteinPolynomial.eval_at_1`,
  `bernsteinPolynomial.derivative_succ`, `bernsteinPolynomial.sum` ($\sum_\nu b_{n,\nu} = 1$) and
  `bernsteinPolynomial.linearIndependent` (over $\mathbb{Q}$), and the continuous functions
  `bernstein n ν : C(I, ℝ)` with `bernstein_nonneg` and the Weierstrass approximation theorem. It
  has neither the recursion, nor a basis statement, nor any curve. The polynomial lemmas of this
  file follow the Mathlib style and are in the namespace `bernsteinPolynomial`.
* The curve `Bezier.curve` takes values in an arbitrary real vector space `E` and needs no norm. The
  control points are a family `P : Fin (n + 1) → E`, and the curve is defined for all
  $t \in \mathbb{R}$.
-/

open Polynomial

namespace bernsteinPolynomial

variable (R : Type*) [CommRing R]

/-- **The Bernstein recursion**: over a commutative ring $R$, for all $n, k \in \mathbb{N}$,
$$b_{n+1,k+1} = (1 - X)\, b_{n,k+1} + X\, b_{n,k}$$
in $R[X]$. This is the recursion of §8.7.1 of [quarteroni2000numerical]. -/
theorem succ_succ (n k : ℕ) :
    bernsteinPolynomial R (n + 1) (k + 1)
      = (1 - X) * bernsteinPolynomial R n (k + 1) + X * bernsteinPolynomial R n k := by
  rcases le_or_gt (k + 1) n with h | h
  · obtain ⟨d, hd⟩ : ∃ d, n - k = d + 1 := ⟨n - (k + 1), by omega⟩
    have hd' : n - (k + 1) = d := by omega
    simp only [bernsteinPolynomial, Nat.choose_succ_succ, Nat.succ_sub_succ, hd, hd']
    push_cast
    ring
  · rw [eq_zero_of_lt R h, mul_zero, zero_add]
    simp only [bernsteinPolynomial, Nat.choose_succ_succ, Nat.choose_eq_zero_of_lt h, add_zero,
      Nat.succ_sub_succ]
    ring

/-- The first column of the Bernstein recursion: over a commutative ring $R$,
$b_{n+1,0} = (1 - X)\, b_{n,0}$ in $R[X]$ for every $n \in \mathbb{N}$. -/
theorem succ_zero (n : ℕ) :
    bernsteinPolynomial R (n + 1) 0 = (1 - X) * bernsteinPolynomial R n 0 := by
  simp only [bernsteinPolynomial, Nat.choose_zero_right, Nat.sub_zero, pow_succ]
  push_cast
  ring

/-- Over a nontrivial commutative ring $R$, the Bernstein polynomial $b_{n,k}$ has degree at most
$n$, for all $n, k \in \mathbb{N}$.

For $k > n$ the polynomial $b_{n,k}$ is $0$, whose degree is $-\infty$. -/
theorem degree_le [Nontrivial R] (n k : ℕ) : (bernsteinPolynomial R n k).degree ≤ n := by
  rcases le_or_gt k n with h | h
  · refine degree_le_of_natDegree_le ?_
    unfold bernsteinPolynomial
    refine natDegree_mul_le.trans ?_
    refine (add_le_add natDegree_mul_le natDegree_pow_le).trans ?_
    rw [natDegree_natCast, natDegree_X_pow, zero_add]
    have h1 : (1 - X : R[X]).natDegree ≤ 1 :=
      (natDegree_sub_le _ _).trans (by rw [natDegree_one, natDegree_X]; simp)
    calc k + (n - k) * (1 - X : R[X]).natDegree ≤ k + (n - k) * 1 := by gcongr
      _ = n := by omega
  · rw [eq_zero_of_lt R h, degree_zero]
    exact bot_le

variable {R}

/-- **The Bernstein polynomials are linearly independent** over any field of characteristic zero:
for a field $F$ of characteristic zero and $n \in \mathbb{N}$, the polynomials
$b_{n,0}, \dots, b_{n,n} \in F[X]$ are linearly independent over $F$.

Mathlib's `bernsteinPolynomial.linearIndependent` is the statement over $\mathbb{Q}$. The proof
is the same: the $(n - k)$-th derivative at $1$ annihilates $b_{n,\nu}$ for $\nu < k$ but not
$b_{n,k}$. -/
theorem linearIndependent' {F : Type*} [Field F] [CharZero F] (n : ℕ) :
    LinearIndependent F fun ν : Fin (n + 1) => bernsteinPolynomial F n ν := by
  suffices ∀ k, k ≤ n + 1 → LinearIndependent F fun ν : Fin k => bernsteinPolynomial F n ν from
    this (n + 1) le_rfl
  intro k
  induction k with
  | zero => exact fun _ => linearIndependent_empty_type
  | succ k ih =>
    intro h
    apply linearIndependent_finSucc'.mpr
    refine ⟨ih (le_of_lt h), ?_⟩
    simp only [add_le_add_iff_right] at h
    simp only [Fin.val_last, Fin.init_def]
    apply Submodule.notMem_span_of_apply_notMem_span_image (@Polynomial.derivative F _ ^ (n - k))
    simp only [not_exists, not_and, Submodule.mem_map, Submodule.span_image _]
    intro p m
    apply_fun Polynomial.eval (1 : F)
    simp only [Module.End.pow_apply]
    suffices (Polynomial.derivative^[n - k] p).eval 1 = 0 by
      rw [this]
      exact (iterate_derivative_at_1_ne_zero F n k h).symm
    refine Submodule.span_induction ?_ ?_ ?_ ?_ m
    · simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
      rintro ⟨a, w⟩
      exact iterate_derivative_at_1_eq_zero_of_lt F n ((tsub_lt_tsub_iff_left_of_le h).mpr w)
    · simp
    · intro x y _ _ hx hy
      simp [hx, hy]
    · intro a x _ hx
      simp [hx]

end bernsteinPolynomial

/-- The Bernstein polynomial $b_{n,k}$, as an element of `polyLE X n`, the space of the restrictions
to $X \subseteq \mathbb{R}$ of the real polynomials of degree at most $n$. -/
noncomputable def bernsteinPolynomial.toPolyLE (X : Set ℝ) (n k : ℕ) : polyLE X n :=
  ⟨(bernsteinPolynomial ℝ n k).toContinuousMapOn X,
    mem_polyLE_iff.mpr ⟨bernsteinPolynomial ℝ n k, bernsteinPolynomial.degree_le ℝ n k,
      fun _ => rfl⟩⟩

/-- **The Bernstein basis**: let $X \subseteq \mathbb{R}$ be an infinite set and $n \in \mathbb{N}$.
There is a basis $(e_k)_{k=0}^{n}$ of the space of the restrictions to $X$ of the real
polynomials of degree at most $n$ such that $e_k(t) = b_{n,k}(t)$ for every $k$ and every
$t \in X$.

This is the statement of §8.7.1 of [quarteroni2000numerical] that $\{b_{n,k}\}$ provides a basis
for $\mathcal{P}_n$. The space is `polyLE X n`, a subspace of `C(X, ℝ)`. -/
theorem bernsteinPolynomial.exists_basis_polyLE {X : Set ℝ} (hX : X.Infinite) (n : ℕ) :
    ∃ B : Module.Basis (Fin (n + 1)) ℝ (polyLE X n),
      ∀ k (t : X), (B k : C(X, ℝ)) t = (bernsteinPolynomial ℝ n k).eval (t : ℝ) := by
  have hli : LinearIndependent ℝ fun k : Fin (n + 1) => bernsteinPolynomial.toPolyLE X n k := by
    refine LinearIndependent.of_comp (polyLE X n).subtype ?_
    have := (bernsteinPolynomial.linearIndependent' (F := ℝ) n).map'
      (Polynomial.toContinuousMapOnAlgHom X).toLinearMap
      (LinearMap.ker_eq_bot.mpr (Polynomial.toContinuousMapOnAlgHom_injective hX))
    exact this
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by rw [finrank_polyLE hX, Fintype.card_fin]),
    fun k t => ?_⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  rfl

namespace Bezier

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}

/-- **The Bézier curve** of the control points $P_0, \dots, P_n$ in a real vector space $E$: for
$t \in \mathbb{R}$,
$$B_n(P; t) = \sum_{k=0}^{n} b_{n,k}(t)\, P_k.$$
This is (8.58) of [quarteroni2000numerical]. -/
noncomputable def curve (P : Fin (n + 1) → E) (t : ℝ) : E :=
  ∑ k : Fin (n + 1), (bernsteinPolynomial ℝ n k).eval t • P k

/-- One step of de Casteljau's construction: for $t \in \mathbb{R}$, the points
$P_0, \dots, P_{n+1}$ give the $n + 1$ points
$$P_{i,1}(t) = (1 - t) P_i + t P_{i+1}, \qquad i = 0, \dots, n,$$
which divide each edge of the control polygon in the ratio $t : (1 - t)$. -/
def casteljauStep (t : ℝ) (P : Fin (n + 2) → E) : Fin (n + 1) → E :=
  fun i => (1 - t) • P i.castSucc + t • P i.succ

/-- **De Casteljau's algorithm** (§8.7.1 of [quarteroni2000numerical]): for $t \in \mathbb{R}$ and
control points $P_0, \dots, P_n$, apply `Bezier.casteljauStep` $n$ times, until one point
remains. This point is $P_{0,n}(t)$. For one control point, the result is that point. -/
def casteljau (t : ℝ) : {n : ℕ} → (Fin (n + 1) → E) → E
  | 0, P => P 0
  | _ + 1, P => casteljau t (casteljauStep t P)

/-- De Casteljau's algorithm applied to one control point $P_0$ gives $P_0$. -/
@[simp]
theorem casteljau_zero (t : ℝ) (P : Fin 1 → E) : casteljau t P = P 0 := rfl

/-- De Casteljau's algorithm applied to $n + 2$ control points is the algorithm applied to the
$n + 1$ points of one step `Bezier.casteljauStep`. -/
theorem casteljau_succ (t : ℝ) (P : Fin (n + 2) → E) :
    casteljau t P = casteljau t (casteljauStep t P) := rfl

/-- The Bézier curve of a single control point $P_0$ is the constant $P_0$. -/
@[simp]
theorem curve_of_one (P : Fin 1 → E) (t : ℝ) : curve P t = P 0 := by
  simp [curve, bernsteinPolynomial]

/-- **The Bézier recursion**: for control points $P_0, \dots, P_{n+1}$ and $t \in \mathbb{R}$,
$$B_{n+1}(P_0, \dots, P_{n+1}; t) = (1 - t)\, B_n(P_0, \dots, P_n; t) + t\, B_n(P_1, \dots,
  P_{n+1}; t).$$

This is the polynomial identity `bernsteinPolynomial.succ_succ` read on the curve. The two
shorter control polygons are `Fin.init P` and `Fin.tail P`. -/
theorem curve_succ (P : Fin (n + 2) → E) (t : ℝ) :
    curve P t = (1 - t) • curve (Fin.init P) t + t • curve (Fin.tail P) t := by
  have hrec : ∀ k : Fin (n + 1), (bernsteinPolynomial ℝ (n + 1) (k.succ : ℕ)).eval t
      = (1 - t) * (bernsteinPolynomial ℝ n ((k : ℕ) + 1)).eval t
        + t * (bernsteinPolynomial ℝ n k).eval t := fun k => by
    rw [Fin.val_succ, bernsteinPolynomial.succ_succ]
    simp
  have h0 : (bernsteinPolynomial ℝ (n + 1) 0).eval t
      = (1 - t) * (bernsteinPolynomial ℝ n 0).eval t := by
    rw [bernsteinPolynomial.succ_zero]
    simp
  have hlast : (bernsteinPolynomial ℝ n (n + 1)).eval t = 0 := by
    rw [bernsteinPolynomial.eq_zero_of_lt ℝ (Nat.lt_succ_self n), eval_zero]
  have h1 : ∑ k : Fin (n + 1), ((1 - t) * (bernsteinPolynomial ℝ n k).eval t) • P k.castSucc
      = ((1 - t) * (bernsteinPolynomial ℝ n 0).eval t) • P 0
        + ∑ k : Fin n,
          ((1 - t) * (bernsteinPolynomial ℝ n ((k : ℕ) + 1)).eval t) • P k.succ.castSucc := by
    rw [Fin.sum_univ_succ]
    simp
  have h2 : ∑ k : Fin (n + 1), ((1 - t) * (bernsteinPolynomial ℝ n ((k : ℕ) + 1)).eval t) • P k.succ
      = ∑ k : Fin n,
          ((1 - t) * (bernsteinPolynomial ℝ n ((k : ℕ) + 1)).eval t) • P k.succ.castSucc := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, hlast, mul_zero, zero_smul, add_zero]
    exact Finset.sum_congr rfl fun k _ => by rw [Fin.succ_castSucc]
  simp only [curve, Finset.smul_sum, smul_smul, Fin.init_def, Fin.tail_def]
  rw [Fin.sum_univ_succ, Fin.val_zero, h0]
  simp_rw [hrec, add_smul, Finset.sum_add_distrib]
  rw [h1, h2]
  abel

/-- For control points $P_0, \dots, P_{n+1}$ and $t \in \mathbb{R}$, the Bézier curve of the points
$P_{0,1}(t), \dots, P_{n,1}(t)$ of one de Casteljau step, evaluated at the same $t$, is
$B_{n+1}(P; t)$. This is the curve version of `bernsteinPolynomial.succ_succ`. -/
theorem curve_casteljauStep (P : Fin (n + 2) → E) (t : ℝ) :
    curve (casteljauStep t P) t = curve P t := by
  rw [curve_succ]
  simp only [curve, casteljauStep, smul_add, Finset.sum_add_distrib, Finset.smul_sum, smul_smul,
    Fin.init_def, Fin.tail_def, mul_comm]

/-- **De Casteljau's algorithm evaluates the Bézier curve** (§8.7.1 of [quarteroni2000numerical]):
for control points $P_0, \dots, P_n$ and $t \in \mathbb{R}$, the result $P_{0,n}(t)$ of
`Bezier.casteljau` is $B_n(P_0, \dots, P_n; t)$. -/
theorem casteljau_eq_curve (P : Fin (n + 1) → E) (t : ℝ) : casteljau t P = curve P t := by
  induction n with
  | zero => simp
  | succ n ih => rw [casteljau_succ, ih, curve_casteljauStep]

/-- The Bézier curve starts at the first control point: $B_n(P; 0) = P_0$. -/
theorem curve_zero (P : Fin (n + 1) → E) : curve P 0 = P 0 := by
  simp only [curve, bernsteinPolynomial.eval_at_0]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    have : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext (by simpa using h))
    rw [ite_eq_right this, zero_smul]
  · simp

/-- The Bézier curve ends at the last control point: $B_n(P; 1) = P_n$. -/
theorem curve_one (P : Fin (n + 1) → E) : curve P 1 = P (Fin.last n) := by
  simp only [curve, bernsteinPolynomial.eval_at_1]
  rw [Finset.sum_eq_single (Fin.last n)]
  · simp
  · intro k _ hk
    have : (k : ℕ) ≠ n := fun h => hk (Fin.ext (by simpa using h))
    rw [ite_eq_right this, zero_smul]
  · simp

/-- **Reversal** (§8.7.1 of [quarteroni2000numerical]): the Bézier curve of the reversed control
polygon $P_n, \dots, P_0$ is the same curve traversed backwards. For every $t \in \mathbb{R}$,
$$B_n(P_n, \dots, P_0; t) = B_n(P_0, \dots, P_n; 1 - t).$$
-/
theorem curve_rev (P : Fin (n + 1) → E) (t : ℝ) : curve (P ∘ Fin.rev) t = curve P (1 - t) := by
  simp only [curve, Function.comp_apply]
  rw [← Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (n + 1)))]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Fin.revPerm_apply, Fin.rev_rev]
  congr 1
  have hk : (k : ℕ) ≤ n := Nat.lt_succ_iff.mp k.isLt
  rw [Fin.val_rev, Nat.add_sub_add_right, ← bernsteinPolynomial.flip ℝ n k hk, eval_comp]
  simp

/-- **The convex-hull property** (§8.7.1 of [quarteroni2000numerical]): for control points
$P_0, \dots, P_n$ and $t \in [0, 1]$, the point $B_n(P; t)$ lies in the convex hull of
$\{P_0, \dots, P_n\}$.

The source describes $B_n(P; t)$ as a weighted average of the points $P_k$: for $t \in [0, 1]$
the weights $b_{n,k}(t)$ are nonnegative and sum to one. -/
theorem curve_mem_convexHull (P : Fin (n + 1) → E) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    curve P t ∈ convexHull ℝ (Set.range P) := by
  refine (convex_convexHull ℝ _).sum_mem (fun k _ => ?_) ?_ fun k _ => subset_convexHull ℝ _
    (Set.mem_range_self k)
  · have := bernstein_nonneg (n := n) (ν := k) (x := ⟨t, ht⟩)
    rwa [bernstein, Polynomial.toContinuousMapOn_apply, Polynomial.toContinuousMap_apply] at this
  · rw [Fin.sum_univ_eq_sum_range (fun k => (bernsteinPolynomial ℝ n k).eval t), ← eval_finsetSum,
      bernsteinPolynomial.sum, eval_one]

/-- **Affine equivariance**: let $E$ and $F$ be real vector spaces, let $L : E \to F$ be linear, and
let $c \in F$. For control points $P_0, \dots, P_n$ in $E$ and $t \in \mathbb{R}$,
$$B_n(L P_0 + c, \dots, L P_n + c; t) = L\, B_n(P; t) + c.$$
This is the invariance under changes of coordinates that motivates parametric curves in §8.7 of
[quarteroni2000numerical]. -/
theorem curve_affine {F : Type*} [AddCommGroup F] [Module ℝ F] (L : E →ₗ[ℝ] F) (c : F)
    (P : Fin (n + 1) → E) (t : ℝ) :
    curve (fun k => L (P k) + c) t = L (curve P t) + c := by
  have hsum : ∑ k : Fin (n + 1), (bernsteinPolynomial ℝ n k).eval t = 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun k => (bernsteinPolynomial ℝ n k).eval t), ← eval_finsetSum,
      bernsteinPolynomial.sum, eval_one]
  simp only [curve, map_sum, map_smul, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hsum,
    one_smul]

end Bezier
