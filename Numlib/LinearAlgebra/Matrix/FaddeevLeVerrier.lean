/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.Charpoly.FaddeevLeVerrier`, with `Matrix.derivative_det`
beside `Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# The Faddeev–LeVerrier recurrence

Let $A$ be an $N \times N$ matrix over a field $K$ of characteristic zero, with characteristic
polynomial $p(X) = \det(XI - A) = \sum_i c_i X^i$. The recurrence of [quarteroni2000numerical] §3.6
(after Faddeev and Faddeeva, *Computational Methods of Linear Algebra*, 1963) $$B_0 = I, \qquad
\alpha_k = \frac{\operatorname{tr}(A B_{k-1})}{k}, \qquad B_k = \alpha_k I - A B_{k-1} \quad (k = 1,
2, \dots)$$ computes the coefficients of $p$ and the inverse of $A$: $\alpha_k = (-1)^k c_{N-k}$ for
$k \le N$, $B_N = 0$, and if $\alpha_N = \det A \ne 0$, then $A^{-1} = B_{N-1} / \alpha_N$.

The proof goes through the **Horner partial sums** $H_k = \sum_{i \le k} c_{N-i} A^{k-i}$, the
evaluation of $p$ at $A$ by Horner's scheme stopped after $k$ steps. They are the coefficients of
the adjugate of the characteristic matrix, $\operatorname{adj}(XI - A) = \sum_{j < N} X^j
H_{N-1-j}$, and $B_k = (-1)^k H_k$. **Jacobi's formula** $(\det M)' =
\operatorname{tr}(\operatorname{adj}(M)\, M')$ for a matrix $M$ of polynomials gives $p' =
\operatorname{tr} \operatorname{adj}(XI - A)$. Read coefficient by coefficient, this is
$\operatorname{tr} H_k = (N - k)\, c_{N-k}$, the trace form of Newton's identities.

## Main definitions

* `Matrix.charpolyHorner`: the Horner partial sums $H_k$.
* `Matrix.faddeevB`, `Matrix.faddeevAlpha`: the matrices $B_k$ and the scalars $\alpha_k$ of the
  recurrence.

## Main results

* `Matrix.derivative_det`: Jacobi's formula $(\det M)' = \operatorname{tr}(\operatorname{adj}(M)\,
  M')$.
* `Matrix.derivative_charpoly`: $p' = \operatorname{tr} \operatorname{adj}(XI - A)$.
* `Matrix.adjugate_charmatrix_eq_sum`: $\operatorname{adj}(XI - A) = \sum_{j < N} X^j H_{N-1-j}$.
* `Matrix.trace_charpolyHorner`: $\operatorname{tr} H_k = (N - k)\, c_{N-k}$ for $k \le N$.
* `Matrix.faddeevB_eq_smul_charpolyHorner`, `Matrix.faddeevAlpha_eq_neg_one_pow_mul_charpoly_coeff`:
  $B_k = (-1)^k H_k$ and $\alpha_k = (-1)^k c_{N-k}$ for $k \le N$.
* `Matrix.faddeevB_card_eq_zero`, `Matrix.faddeevAlpha_card_eq_det`: $B_N = 0$ and
  $\alpha_N = \det A$.
* `Matrix.faddeevLeverrier_inv`: if $\alpha_N \ne 0$, then $A^{-1} = B_{N-1} / \alpha_N$.

## Implementation notes

* The signs alternate. Since $B_{k+1} = \alpha_{k+1} I - A B_k$ subtracts, the unsigned forms
  $B_k = H_k$ and $\alpha_k = -c_{N-k}$ fail already at $k = 1$. For $A = \operatorname{diag}(a, b)$
  the characteristic polynomial is $X^2 - (a + b) X + ab$, so
  $H_1 = A + c_1 I = \operatorname{diag}(-b, -a)$. The recurrence gives
  $\alpha_1 = \operatorname{tr} A = a + b$ and $B_1 = \alpha_1 I - A = \operatorname{diag}(b, a) =
  -H_1$, and then $\alpha_2 = ab = +c_0$. [quarteroni2000numerical] §3.6 prints only the recurrence,
  $B_N = 0$ and $A^{-1} = B_{N-1} / \alpha_N$, which have no signs, so nothing here contradicts the
  source.
* The recurrence sets $\alpha_0 = 1$, the leading coefficient of $p$, so that
  $\alpha_k = (-1)^k c_{N-k}$ holds from $k = 0$ on.
* The closed forms hold for $k \le N$ only. For $k > N$ the recurrence gives zeros, while the
  truncated subtraction $N - k$ of natural numbers stays at $0$.
* Jacobi's formula is proved from the Leibniz expansion of the determinant and the product rule. The
  terms in which the entry in column $j$ is differentiated add up to the determinant with column $j$
  replaced by its derivative, which Cramer's rule evaluates.
* $N$ is `Fintype.card n` and $c_i$ is `A.charpoly.coeff i`. The characteristic matrix $XI - A$ is
  `Matrix.charmatrix A`. The adjugate is `Matrix.adjugate`.
-/

open Polynomial Finset

namespace Matrix

/-! ### Jacobi's formula -/

section Jacobi

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

/-- **Jacobi's formula.** Let $R$ be a commutative ring and let $M$ be a square matrix over $R[X]$.
The derivative of $\det M$ is $$(\det M)' = \operatorname{tr}(\operatorname{adj}(M)\, M'),$$
where $M'$ is the entrywise derivative of $M$.

By the Leibniz expansion and the product rule, the terms in which the entry in column $j$ is
differentiated add up to the determinant with column $j$ replaced by its derivative. Cramer's
rule evaluates this determinant as $(\operatorname{adj}(M)\, M')_{jj}$. -/
theorem derivative_det (M : Matrix n n R[X]) :
    derivative M.det = trace (adjugate M * M.map derivative) := by
  have hcol : ∀ σ : Equiv.Perm n, ∀ j : n,
      ∏ i, (M.updateCol j fun r => derivative (M r j)) (σ i) i
        = (∏ i ∈ univ.erase j, M (σ i) i) * derivative (M (σ j) j) := by
    intro σ j
    rw [← Finset.prod_erase_mul univ _ (mem_univ j), updateCol_self]
    congr 1
    exact Finset.prod_congr rfl fun i hi => updateCol_ne (Finset.ne_of_mem_erase hi)
  rw [det_apply', map_sum]
  simp_rw [derivative_mul, derivative_intCast, zero_mul, zero_add, derivative_prod_finset,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [diag_apply, Matrix.mul_apply]
  have h := det_apply' (M.updateCol j fun r => derivative (M r j))
  simp_rw [hcol] at h
  rw [← h, ← cramer_apply, cramer_eq_adjugate_mulVec, mulVec_apply_eq_sum]
  simp only [map_apply]

/-- The entrywise derivative of the characteristic matrix $XI - A$ is the identity. -/
theorem charmatrix_map_derivative (A : Matrix n n R) : (charmatrix A).map derivative = 1 := by
  refine Matrix.ext fun i j => ?_
  rw [map_apply, charmatrix_apply, derivative_sub, derivative_C, sub_zero, diagonal_apply,
    Matrix.one_apply]
  split_ifs
  · exact derivative_X
  · exact derivative_zero

/-- **Jacobi's formula for the characteristic polynomial.** For a square matrix $A$ over a
commutative ring, $p' = \operatorname{tr} \operatorname{adj}(XI - A)$, where $p$ is the
characteristic polynomial of $A$. -/
theorem derivative_charpoly (A : Matrix n n R) :
    derivative A.charpoly = trace (adjugate (charmatrix A)) := by
  rw [charpoly, derivative_det, charmatrix_map_derivative, Matrix.mul_one]

end Jacobi

/-! ### Horner's partial sums of the characteristic polynomial -/

section Horner

variable {R : Type*} [CommRing R] [Nontrivial R] {n : Type*} [Fintype n] [DecidableEq n]
  (A : Matrix n n R)

/-- Let $A$ be an $N \times N$ matrix over a nontrivial commutative ring, with characteristic
polynomial $p = \sum_i c_i X^i$. The **Horner partial sum** of $p$ at $A$ after $k$ steps is
$$H_k = \sum_{i \le k} c_{N-i} A^{k-i}.$$

It starts at $H_0 = I$ and ends at $H_N = p(A) = 0$, and the $H_k$ are the coefficients of
$\operatorname{adj}(XI - A)$. For $i > N$ the index $N - i$ is $0$ by truncated subtraction. -/
noncomputable def charpolyHorner (k : ℕ) : Matrix n n R :=
  ∑ i ∈ range (k + 1), A.charpoly.coeff (Fintype.card n - i) • A ^ (k - i)

/-- The first Horner partial sum is the identity: $H_0 = I$. -/
@[simp]
theorem charpolyHorner_zero : charpolyHorner A 0 = 1 := by
  rw [charpolyHorner, zero_add, range_one, sum_singleton, Nat.sub_zero, Nat.sub_zero, pow_zero,
    ← charpoly_natDegree_eq_dim A, (charpoly_monic A).coeff_natDegree, one_smul]

omit [Nontrivial R] in
/-- **Horner's step**: $H_{k+1} = A H_k + c_{N-(k+1)} I$. -/
theorem charpolyHorner_succ (k : ℕ) :
    charpolyHorner A (k + 1)
      = A * charpolyHorner A k + A.charpoly.coeff (Fintype.card n - (k + 1)) • 1 := by
  rw [charpolyHorner, charpolyHorner, Finset.sum_range_succ, Finset.mul_sum, Nat.sub_self,
    pow_zero]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Matrix.mul_smul, ← pow_succ', Nat.succ_sub (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))]

/-- **Cayley–Hamilton in Horner form**: the $N$-th Horner partial sum is $H_N = p(A) = 0$. -/
theorem charpolyHorner_card : charpolyHorner A (Fintype.card n) = 0 := by
  have h := aeval_self_charpoly A
  rw [aeval_eq_sum_range, charpoly_natDegree_eq_dim, ← Finset.sum_range_reflect] at h
  rw [charpolyHorner, ← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.add_sub_cancel]

/-- The last Horner step: if $N \ge 1$, then $A H_{N-1} = -c_0 I$. -/
theorem mul_charpolyHorner_pred (hn : 0 < Fintype.card n) :
    A * charpolyHorner A (Fintype.card n - 1) = -(A.charpoly.coeff 0 • 1) := by
  have h := charpolyHorner_succ A (Fintype.card n - 1)
  rw [Nat.sub_add_cancel hn, charpolyHorner_card, Nat.sub_self] at h
  exact eq_neg_of_add_eq_zero_left h.symm

end Horner


/-! ### The adjugate of the characteristic matrix -/

section Adjugate

variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n K)

/-- Over a field $K$, the characteristic matrix of $A$ is $XI - A$ with $A$ embedded in $K[X]$. -/
private theorem charmatrix_eq_smul_one_sub :
    charmatrix A = (X : K[X]) • (1 : Matrix n n K[X]) - A.map C := by
  refine Matrix.ext fun i j => ?_
  rw [charmatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, map_apply,
      diagonal_apply]
  split_ifs <;> simp

omit [Fintype n] in
/-- The embedding of $K$ into $K[X]$ carries $cI$ to $cI$. -/
private theorem map_C_smul_one (c : K) :
    (c • (1 : Matrix n n K)).map C = C c • (1 : Matrix n n K[X]) := by
  refine Matrix.ext fun i j => ?_
  rw [map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply,
      smul_eq_mul, smul_eq_mul]
  split_ifs <;> simp

/-- **The adjugate of the characteristic matrix.** Let $A$ be an $N \times N$ matrix over a field
$K$. Then $$\operatorname{adj}(XI - A) = \sum_{j < N} X^j H_{N-1-j},$$ where $H_k$ are the
Horner partial sums of the characteristic polynomial $p$ of $A$.

The right side $Q$ satisfies $(XI - A) Q = pI$ by telescoping, from
$H_{k+1} = A H_k + c_{N-k-1} I$, $H_0 = I$ and $H_N = 0$. Since $p \ne 0$, the adjugate is the
only such matrix. -/
theorem adjugate_charmatrix_eq_sum :
    adjugate (charmatrix A) = ∑ j ∈ range (Fintype.card n),
      (X : K[X]) ^ j • (charpolyHorner A (Fintype.card n - 1 - j)).map C := by
  obtain ⟨N, hN⟩ : ∃ N, N = Fintype.card n := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix n n K[X],
    Q = ∑ j ∈ range N, (X : K[X]) ^ j • (charpolyHorner A (N - 1 - j)).map C := ⟨_, rfl⟩
  rw [← hN, ← hQ]
  -- the Horner step in the form the telescoping needs
  have hH : ∀ j, j < N → A * charpolyHorner A (N - 1 - j)
      = charpolyHorner A (N - j) - A.charpoly.coeff j • 1 := by
    intro j hj
    have h := charpolyHorner_succ A (N - 1 - j)
    rw [show N - 1 - j + 1 = N - j by omega, ← hN, show N - (N - j) = j by omega] at h
    rw [h, add_sub_cancel_right]
  -- `(X • 1 - A) Q = p • 1`
  have hmul : charmatrix A * Q = A.charpoly • (1 : Matrix n n K[X]) := by
    obtain ⟨F, hF⟩ : ∃ F : ℕ → Matrix n n K[X],
      F = fun j => (X : K[X]) ^ j • (charpolyHorner A (N - j)).map C := ⟨_, rfl⟩
    have h1 : charmatrix A * Q
        = ∑ j ∈ range N, (F (j + 1) - F j + (X ^ j * C (A.charpoly.coeff j)) • 1) := by
      rw [hQ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [charmatrix_eq_smul_one_sub, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul,
        Matrix.mul_smul, ← Matrix.map_mul, hH j (Finset.mem_range.1 hj),
        Matrix.map_sub _ (map_sub C), map_C_smul_one, smul_sub, smul_smul, hF]
      simp only [Nat.sub_sub, pow_succ, smul_smul, mul_comm X]
      abel_nf
    have hF0 : F 0 = 0 := by
      rw [hF]
      simp only [pow_zero, one_smul, Nat.sub_zero, hN, charpolyHorner_card]
      exact Matrix.map_zero C C_0
    have hFN : F N = (X : K[X]) ^ N • 1 := by
      rw [hF]
      simp only [Nat.sub_self, charpolyHorner_zero]
      rw [Matrix.map_one C C_0 C_1]
    have hsum : ∑ j ∈ range N, (F (j + 1) - F j) = F N - F 0 := by
      rw [Finset.sum_range_sub]
    have hp : A.charpoly = ∑ i ∈ range N, C (A.charpoly.coeff i) * X ^ i + X ^ N := by
      have hcN : A.charpoly.coeff N = 1 := by
        rw [hN, ← charpoly_natDegree_eq_dim A]
        exact (charpoly_monic A).coeff_natDegree
      conv_lhs => rw [as_sum_range_C_mul_X_pow A.charpoly, charpoly_natDegree_eq_dim, ← hN,
        Finset.sum_range_succ, hcN, C_1, one_mul]
    rw [h1, Finset.sum_add_distrib, hsum, hF0, hFN, sub_zero, ← Finset.sum_smul, ← add_smul,
      add_comm]
    conv_rhs => rw [hp]
    congr 2
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  -- uniqueness: cancel the nonzero polynomial `p` entrywise
  have hadj : charmatrix A * adjugate (charmatrix A) = A.charpoly • (1 : Matrix n n K[X]) :=
    mul_adjugate _
  have hcancel : A.charpoly • adjugate (charmatrix A) = A.charpoly • Q := by
    have h := congrArg (fun M => adjugate (charmatrix A) * M) (hadj.trans hmul.symm)
    simp only [← Matrix.mul_assoc, adjugate_mul, Matrix.smul_mul, Matrix.one_mul] at h
    exact h
  refine Matrix.ext fun i j => ?_
  have h := congrFun (congrFun hcancel i) j
  rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul] at h
  exact mul_left_cancel₀ (charpoly_monic A).ne_zero h

end Adjugate


/-! ### The trace identities -/

section Trace

variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n K)

/-- Jacobi's formula on the adjugate: $p' = \sum_{j < N} X^j \operatorname{tr} H_{N-1-j}$. -/
private theorem derivative_charpoly_eq_sum :
    derivative A.charpoly = ∑ j ∈ range (Fintype.card n),
      (X : K[X]) ^ j * C (trace (charpolyHorner A (Fintype.card n - 1 - j))) := by
  rw [derivative_charpoly, adjugate_charmatrix_eq_sum, trace_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [trace_smul, smul_eq_mul, ← AddMonoidHom.map_trace]

/-- **The trace of a Horner partial sum.** Let $A$ be an $N \times N$ matrix over a field. For
$k \le N$, $$\operatorname{tr} H_k = (N - k)\, c_{N-k}.$$ This is the trace form of Newton's
identities.

It is Jacobi's formula $p' = \operatorname{tr} \operatorname{adj}(XI - A)$ read coefficient by
coefficient. -/
theorem trace_charpolyHorner {k : ℕ} (hk : k ≤ Fintype.card n) :
    trace (charpolyHorner A k)
      = ((Fintype.card n - k : ℕ) : K) * A.charpoly.coeff (Fintype.card n - k) := by
  obtain ⟨N, hN⟩ : ∃ N, N = Fintype.card n := ⟨_, rfl⟩
  rw [← hN] at hk ⊢
  rcases eq_or_lt_of_le hk with rfl | hk
  · rw [hN, charpolyHorner_card, trace_zero, Nat.sub_self, Nat.cast_zero, zero_mul]
  · have h := congrArg (fun q : K[X] => q.coeff (N - 1 - k)) (derivative_charpoly_eq_sum A)
    simp only [coeff_derivative, finsetSum_coeff, ← hN] at h
    rw [Finset.sum_eq_single (N - 1 - k)] at h
    · rw [mul_comm (X ^ _), coeff_C_mul_X_pow, ite_eq_left rfl,
        show N - 1 - (N - 1 - k) = k by omega] at h
      have e : N - 1 - k + 1 = N - k := by omega
      rw [← h, ← Nat.cast_succ, Nat.succ_eq_add_one, e, mul_comm]
    · intro i _ hi
      rw [mul_comm (X ^ _), coeff_C_mul_X_pow, ite_eq_right (Ne.symm hi)]
    · intro h'
      exact absurd (Finset.mem_range.2 (by omega)) h'

/-- **Newton's identities in trace form.** Let $A$ be an $N \times N$ matrix over a field. For
$k < N$, $$\operatorname{tr}(A H_k) = -(k + 1)\, c_{N-(k+1)}.$$

This follows from $H_{k+1} = A H_k + c_{N-(k+1)} I$ and the traces of the two Horner sums. -/
theorem trace_mul_charpolyHorner {k : ℕ} (hk : k < Fintype.card n) :
    trace (A * charpolyHorner A k)
      = -(((k + 1 : ℕ) : K) * A.charpoly.coeff (Fintype.card n - (k + 1))) := by
  have h := congrArg trace (charpolyHorner_succ A k)
  rw [trace_add, trace_smul, trace_one, trace_charpolyHorner A hk, smul_eq_mul,
    Nat.cast_sub hk] at h
  push_cast at h ⊢
  linear_combination -h

end Trace

/-! ### The Faddeev–LeVerrier recurrence -/

section Recurrence

variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n K)

/-- The pair $(B_k, \alpha_k)$ of the Faddeev–LeVerrier recurrence for a square matrix $A$ over a
field: $B_0 = I$, $\alpha_0 = 1$, and $$\alpha_{k+1} = \frac{\operatorname{tr}(A B_k)}{k + 1},
\qquad B_{k+1} = \alpha_{k+1} I - A B_k.$$

The value $\alpha_0 = 1$ is the leading coefficient of the characteristic polynomial, so that
the closed form $\alpha_k = (-1)^k c_{N-k}$ holds from $k = 0$ on. -/
noncomputable def faddeev : ℕ → Matrix n n K × K
  | 0 => (1, 1)
  | k + 1 =>
    let α := trace (A * (faddeev k).1) / (k + 1)
    (α • 1 - A * (faddeev k).1, α)

/-- The matrices $B_k$ of the Faddeev–LeVerrier recurrence ([quarteroni2000numerical] §3.6):
$B_0 = I$ and $B_{k+1} = \alpha_{k+1} I - A B_k$. -/
noncomputable def faddeevB (k : ℕ) : Matrix n n K := (faddeev A k).1

/-- The scalars $\alpha_k$ of the Faddeev–LeVerrier recurrence ([quarteroni2000numerical] §3.6):
$\alpha_0 = 1$ and $\alpha_{k+1} = \operatorname{tr}(A B_k) / (k + 1)$. -/
noncomputable def faddeevAlpha (k : ℕ) : K := (faddeev A k).2

/-- The recurrence starts from $B_0 = I$. -/
@[simp] theorem faddeevB_zero : faddeevB A 0 = 1 := rfl

/-- The recurrence starts from $\alpha_0 = 1$, the leading coefficient of the characteristic
polynomial. -/
@[simp] theorem faddeevAlpha_zero : faddeevAlpha A 0 = 1 := rfl

/-- The scalar step of the recurrence: $\alpha_{k+1} = \operatorname{tr}(A B_k) / (k + 1)$. -/
theorem faddeevAlpha_succ (k : ℕ) :
    faddeevAlpha A (k + 1) = trace (A * faddeevB A k) / (k + 1) := rfl

/-- The matrix step of the recurrence: $B_{k+1} = \alpha_{k+1} I - A B_k$. -/
theorem faddeevB_succ (k : ℕ) :
    faddeevB A (k + 1) = faddeevAlpha A (k + 1) • 1 - A * faddeevB A k := rfl

variable [CharZero K]

/-- Over a field of characteristic zero, for $k \le N$: $B_k = (-1)^k H_k$ and
$\alpha_k = (-1)^k c_{N-k}$. -/
private theorem faddeev_eq {k : ℕ} (hk : k ≤ Fintype.card n) :
    faddeevB A k = (-1 : K) ^ k • charpolyHorner A k ∧
      faddeevAlpha A k = (-1) ^ k * A.charpoly.coeff (Fintype.card n - k) := by
  induction k with
  | zero =>
    refine ⟨by simp, ?_⟩
    rw [faddeevAlpha_zero, pow_zero, one_mul, Nat.sub_zero, ← charpoly_natDegree_eq_dim A,
      (charpoly_monic A).coeff_natDegree]
  | succ k ih =>
    obtain ⟨hB, -⟩ := ih (Nat.le_of_succ_le hk)
    have hα : faddeevAlpha A (k + 1)
        = (-1) ^ (k + 1) * A.charpoly.coeff (Fintype.card n - (k + 1)) := by
      rw [faddeevAlpha_succ, hB, Matrix.mul_smul, trace_smul, smul_eq_mul,
        trace_mul_charpolyHorner A (Nat.lt_of_succ_le hk)]
      have hne : ((k : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      push_cast
      field_simp
      ring
    refine ⟨?_, hα⟩
    rw [faddeevB_succ, hα, hB, charpolyHorner_succ, Matrix.mul_smul, pow_succ]
    module

/-- Let $A$ be an $N \times N$ matrix over a field of characteristic zero. For $k \le N$, the
Faddeev–LeVerrier matrices are the signed Horner partial sums: $$B_k = (-1)^k H_k, \qquad H_k =
\sum_{i \le k} c_{N-i} A^{k-i}.$$
-/
theorem faddeevB_eq_smul_charpolyHorner {k : ℕ} (hk : k ≤ Fintype.card n) :
    faddeevB A k = (-1 : K) ^ k • charpolyHorner A k :=
  (faddeev_eq A hk).1

/-- Let $A$ be an $N \times N$ matrix over a field of characteristic zero. For $k \le N$, the
Faddeev–LeVerrier scalars are the signed coefficients of the characteristic polynomial:
$$\alpha_k = (-1)^k c_{N-k}.$$ In particular $\alpha_1 = \operatorname{tr} A$ and
$\alpha_N = \det A$ (`Matrix.faddeevAlpha_card_eq_det`). -/
theorem faddeevAlpha_eq_neg_one_pow_mul_charpoly_coeff {k : ℕ} (hk : k ≤ Fintype.card n) :
    faddeevAlpha A k = (-1) ^ k * A.charpoly.coeff (Fintype.card n - k) :=
  (faddeev_eq A hk).2

/-- **The recurrence terminates**: over a field of characteristic zero, $B_N = 0$, by the
Cayley–Hamilton theorem. -/
theorem faddeevB_card_eq_zero : faddeevB A (Fintype.card n) = 0 := by
  rw [faddeevB_eq_smul_charpolyHorner A le_rfl, charpolyHorner_card, smul_zero]

/-- Over a field of characteristic zero, the last scalar of the recurrence is the determinant:
$\alpha_N = \det A$. -/
theorem faddeevAlpha_card_eq_det : faddeevAlpha A (Fintype.card n) = A.det := by
  rw [faddeevAlpha_eq_neg_one_pow_mul_charpoly_coeff A le_rfl, Nat.sub_self,
    det_eq_sign_charpoly_coeff]

/-- **The Faddeev–LeVerrier formula for the inverse** ([quarteroni2000numerical] §3.6). Let $A$ be
an $N \times N$ matrix over a field of characteristic zero with $\alpha_N \ne 0$, that is, with
$A$ nonsingular. Then $$A^{-1} = \alpha_N^{-1} B_{N-1}.$$

Since $B_N = 0$, the last step of the recurrence reads $A B_{N-1} = \alpha_N I$. -/
theorem faddeevLeverrier_inv (h : faddeevAlpha A (Fintype.card n) ≠ 0) :
    A⁻¹ = (faddeevAlpha A (Fintype.card n))⁻¹ • faddeevB A (Fintype.card n - 1) := by
  obtain ⟨N, hN⟩ : ∃ N, N = Fintype.card n := ⟨_, rfl⟩
  rw [← hN] at h ⊢
  rcases N with _ | N
  · have : IsEmpty n := Fintype.card_eq_zero_iff.1 hN.symm
    exact Subsingleton.elim _ _
  · have hB := faddeevB_card_eq_zero A
    rw [← hN, faddeevB_succ, sub_eq_zero] at hB
    refine inv_eq_right_inv ?_
    rw [Matrix.mul_smul, Nat.add_sub_cancel, ← hB, smul_smul, inv_mul_cancel₀ h, one_smul]

end Recurrence

end Matrix
