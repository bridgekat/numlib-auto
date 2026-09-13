import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.RingTheory.Polynomial.Bernstein
import Numlib.Approximation.Chebyshev

/-!
# Bernstein polynomials and Bézier curves

The recursion `b_{n+1,k+1} = (1 - X) b_{n,k+1} + X b_{n,k}` of the Bernstein polynomials, their
degree bound and their basis property, and Bézier curves `B_n(P; t) = ∑_k b_{n,k}(t) P_k` with de
Casteljau's evaluation, the endpoint, reversal, convex-hull and affine-equivariance properties.
The material is [quarteroni2000numerical] §8.7.1 and Farin, *Curves and Surfaces for CAGD*,
chapters 4–5.

Mathlib has `bernsteinPolynomial R n ν : R[X]` with `eval_at_0`, `eval_at_1`, `derivative_succ`,
`sum` (`∑_ν b_{n,ν} = 1`), `linearIndependent` (over `ℚ`), and the continuous functions
`bernstein n ν : C(I, ℝ)` with `bernstein_nonneg` and the Weierstrass approximation; it has neither
the recursion nor a basis statement nor any curve. The polynomial lemmas below are Mathlib-shaped
and live in the `bernsteinPolynomial` namespace; the curve is `Bezier.curve` in a real vector space
`E`, and needs no norm at all.

This module is separate from the B-spline theory because nothing here needs a knot sequence: the
Bernstein basis is the B-spline basis on the two knots `0, 1` each of multiplicity `n + 1`.

## Main definitions

* `Bezier.curve P t` — the Bézier curve of the control points `P : Fin (n + 1) → E`.
* `Bezier.casteljauStep`, `Bezier.casteljau` — de Casteljau's algorithm.

## Main results

* `bernsteinPolynomial.succ_succ`, `bernsteinPolynomial.succ_zero` — the recursion.
* `bernsteinPolynomial.linearIndependent'` — linear independence over any field of characteristic
  zero (Mathlib's `bernsteinPolynomial.linearIndependent` is over `ℚ`).
* `finrank_polyLE` — `dim 𝒫_n = n + 1` on an infinite subset of the line.
* `bernsteinPolynomial.exists_basis_polyLE` — the Bernstein polynomials of degree `n` form a basis
  of the polynomials of degree at most `n` on any infinite subset of the line.
* `Bezier.casteljau_eq_curve` — de Casteljau's algorithm evaluates the Bézier curve.
* `Bezier.curve_zero`, `Bezier.curve_one`, `Bezier.curve_rev`, `Bezier.curve_mem_convexHull`,
  `Bezier.curve_affine` — the endpoint, reversal, convex-hull and affine-equivariance properties.
-/

open Polynomial

namespace bernsteinPolynomial

variable (R : Type*) [CommRing R]

/-- **The Bernstein recursion** ([quarteroni2000numerical] §8.7.1):
`b_{n+1,k+1} = (1 - X) b_{n,k+1} + X b_{n,k}`. -/
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

/-- The first column of the Bernstein recursion: `b_{n+1,0} = (1 - X) b_{n,0}`. -/
theorem succ_zero (n : ℕ) :
    bernsteinPolynomial R (n + 1) 0 = (1 - X) * bernsteinPolynomial R n 0 := by
  simp only [bernsteinPolynomial, Nat.choose_zero_right, Nat.sub_zero, pow_succ]
  push_cast
  ring

/-- A Bernstein polynomial of order `n` has degree at most `n`. -/
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

/-- **The Bernstein polynomials are linearly independent** over any field of characteristic zero.
Mathlib's `bernsteinPolynomial.linearIndependent` is the statement over `ℚ`; the proof is the same:
the `(n - k)`-th derivative at `1` annihilates `b_{n,ν}` for `ν < k` and not `b_{n,k}`. -/
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

/-- The restriction of polynomial functions to an infinite set is injective: a nonzero polynomial
has finitely many roots. -/
theorem Polynomial.toContinuousMapOnAlgHom_injective {X : Set ℝ} (hX : X.Infinite) :
    Function.Injective (Polynomial.toContinuousMapOnAlgHom X) := by
  intro p q hpq
  rw [← sub_eq_zero]
  refine Polynomial.eq_zero_of_infinite_isRoot _ (hX.mono fun x hx => ?_)
  have := congrArg (fun g : C(X, ℝ) => g ⟨x, hx⟩) hpq
  simp only [Polynomial.toContinuousMapOnAlgHom_apply, Polynomial.toContinuousMapOn_apply,
    Polynomial.toContinuousMap_apply] at this
  simp [Polynomial.IsRoot, this]

/-- **The dimension of the polynomials of degree at most `n`** on an infinite subset of the line
is `n + 1`: the restriction of `Polynomial.degreeLT ℝ (n + 1)` is injective there. -/
theorem finrank_polyLE {X : Set ℝ} (hX : X.Infinite) (n : ℕ) :
    Module.finrank ℝ (polyLE X n) = n + 1 := by
  have h : polyLE X n
      = (Polynomial.degreeLT ℝ (n + 1)).map (Polynomial.toContinuousMapOnAlgHom X).toLinearMap := by
    rw [polyLE, Polynomial.degreeLT_succ_eq_degreeLE]
  rw [h, LinearEquiv.finrank_eq
      (Submodule.equivMapOfInjective _ (Polynomial.toContinuousMapOnAlgHom_injective hX) _).symm,
    LinearEquiv.finrank_eq (Polynomial.degreeLTEquiv ℝ (n + 1)), Module.finrank_fin_fun]

/-- The Bernstein polynomial `b_{n,k}`, as an element of the polynomials of degree at most `n` on
`X ⊆ ℝ`. -/
noncomputable def bernsteinPolynomial.toPolyLE (X : Set ℝ) (n k : ℕ) : polyLE X n :=
  ⟨(bernsteinPolynomial ℝ n k).toContinuousMapOn X,
    mem_polyLE_iff.mpr ⟨bernsteinPolynomial ℝ n k, bernsteinPolynomial.degree_le ℝ n k,
      fun _ => rfl⟩⟩

/-- **The Bernstein basis** ([quarteroni2000numerical] §8.7.1, "`{b_{n,k}}` provides a basis for
`𝒫_n`"): on any infinite `X ⊆ ℝ` there is a basis of the polynomials of degree at most `n` whose
`k`-th vector is `t ↦ b_{n,k}(t)`. -/
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

/-- **The Bézier curve** ([quarteroni2000numerical] (8.58)) of the control points `P₀, …, P_n` in
a real vector space: `B_n(P; t) = ∑_k b_{n,k}(t) P_k`. -/
noncomputable def curve (P : Fin (n + 1) → E) (t : ℝ) : E :=
  ∑ k : Fin (n + 1), (bernsteinPolynomial ℝ n k).eval t • P k

/-- One step of de Casteljau's construction: the points `P_{i,1}(t) = (1 - t) P_i + t P_{i+1}` of
the polygon obtained by dividing every edge in the ratio `t : 1 - t`. -/
def casteljauStep (t : ℝ) (P : Fin (n + 2) → E) : Fin (n + 1) → E :=
  fun i => (1 - t) • P i.castSucc + t • P i.succ

/-- **De Casteljau's algorithm** ([quarteroni2000numerical] §8.7.1): iterate `casteljauStep` until
one point remains, the point `P_{0,n}(t)`. -/
def casteljau (t : ℝ) : {n : ℕ} → (Fin (n + 1) → E) → E
  | 0, P => P 0
  | _ + 1, P => casteljau t (casteljauStep t P)

@[simp]
theorem casteljau_zero (t : ℝ) (P : Fin 1 → E) : casteljau t P = P 0 := rfl

theorem casteljau_succ (t : ℝ) (P : Fin (n + 2) → E) :
    casteljau t P = casteljau t (casteljauStep t P) := rfl

/-- The Bézier curve of a single control point is that point. -/
@[simp]
theorem curve_of_one (P : Fin 1 → E) (t : ℝ) : curve P t = P 0 := by
  simp [curve, bernsteinPolynomial]

/-- **The Bézier recursion**: `B_n(P₀, …, P_n; t) = (1 - t) B_{n-1}(P₀, …, P_{n-1}; t) +
t B_{n-1}(P₁, …, P_n; t)`, the polynomial identity `bernsteinPolynomial.succ_succ` read on the
curve. -/
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

/-- The Bézier curve of the stepped polygon is the original Bézier curve: the curve version of
`bernsteinPolynomial.succ_succ`. -/
theorem curve_casteljauStep (P : Fin (n + 2) → E) (t : ℝ) :
    curve (casteljauStep t P) t = curve P t := by
  rw [curve_succ]
  simp only [curve, casteljauStep, smul_add, Finset.sum_add_distrib, Finset.smul_sum, smul_smul,
    Fin.init_def, Fin.tail_def, mul_comm]

/-- **De Casteljau's algorithm evaluates the Bézier curve** ([quarteroni2000numerical] §8.7.1):
`P_{0,n}(t) = B_n(P₀, …, P_n; t)`. -/
theorem casteljau_eq_curve (P : Fin (n + 1) → E) (t : ℝ) : casteljau t P = curve P t := by
  induction n with
  | zero => simp
  | succ n ih => rw [casteljau_succ, ih, curve_casteljauStep]

/-- The Bézier curve starts at the first control point. -/
theorem curve_zero (P : Fin (n + 1) → E) : curve P 0 = P 0 := by
  simp only [curve, bernsteinPolynomial.eval_at_0]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    have : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext (by simpa using h))
    rw [ite_eq_right this, zero_smul]
  · simp

/-- The Bézier curve ends at the last control point. -/
theorem curve_one (P : Fin (n + 1) → E) : curve P 1 = P (Fin.last n) := by
  simp only [curve, bernsteinPolynomial.eval_at_1]
  rw [Finset.sum_eq_single (Fin.last n)]
  · simp
  · intro k _ hk
    have : (k : ℕ) ≠ n := fun h => hk (Fin.ext (by simpa using h))
    rw [ite_eq_right this, zero_smul]
  · simp

/-- **Reversal** ([quarteroni2000numerical] §8.7.1): the Bézier curve of the reversed control
polygon `P_n, …, P₀` is the same curve traversed backwards. -/
theorem curve_rev (P : Fin (n + 1) → E) (t : ℝ) : curve (P ∘ Fin.rev) t = curve P (1 - t) := by
  simp only [curve, Function.comp_apply]
  rw [← Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (n + 1)))]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Fin.revPerm_apply, Fin.rev_rev]
  congr 1
  have hk : (k : ℕ) ≤ n := Nat.lt_succ_iff.mp k.isLt
  rw [Fin.val_rev, Nat.add_sub_add_right, ← bernsteinPolynomial.flip ℝ n k hk, eval_comp]
  simp

/-- **The convex-hull property** ([quarteroni2000numerical] §8.7.1, "a weighted average of the
points `P_k`"): for `t ∈ [0, 1]` the point `B_n(P; t)` lies in the convex hull of the control
polygon, the Bernstein weights being nonnegative and summing to one. -/
theorem curve_mem_convexHull (P : Fin (n + 1) → E) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    curve P t ∈ convexHull ℝ (Set.range P) := by
  refine (convex_convexHull ℝ _).sum_mem (fun k _ => ?_) ?_ fun k _ => subset_convexHull ℝ _
    (Set.mem_range_self k)
  · have := bernstein_nonneg (n := n) (ν := k) (x := ⟨t, ht⟩)
    rwa [bernstein, Polynomial.toContinuousMapOn_apply, Polynomial.toContinuousMap_apply] at this
  · rw [Fin.sum_univ_eq_sum_range (fun k => (bernsteinPolynomial ℝ n k).eval t), ← eval_finsetSum,
      bernsteinPolynomial.sum, eval_one]

/-- **Affine equivariance**: Bézier curves commute with affine maps of the control points, which is
the invariance under changes of coordinates that motivates parametric curves in
[quarteroni2000numerical] §8.7. -/
theorem curve_affine {F : Type*} [AddCommGroup F] [Module ℝ F] (L : E →ₗ[ℝ] F) (c : F)
    (P : Fin (n + 1) → E) (t : ℝ) :
    curve (fun k => L (P k) + c) t = L (curve P t) + c := by
  have hsum : ∑ k : Fin (n + 1), (bernsteinPolynomial ℝ n k).eval t = 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun k => (bernsteinPolynomial ℝ n k).eval t), ← eval_finsetSum,
      bernsteinPolynomial.sum, eval_one]
  simp only [curve, map_sum, map_smul, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hsum,
    one_smul]

end Bezier
