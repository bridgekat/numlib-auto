/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.QuarteroniSaccoSaleri.Chapter03.Section05

/-!
# Quarteroni, Sacco and Saleri, Section 3.7: Banded systems

This module formalizes Section 3.7 of [quarteroni2000numerical]. The LU factorization keeps the band
of a matrix: if $A$ has lower bandwidth $p$ or upper bandwidth $q$, then so does $L$ or $U$
(Property 3.4). For a tridiagonal matrix $A$ with diagonal $a_i$, subdiagonal $b_i$ and
superdiagonal $c_i$, the factors are bidiagonal, and the Thomas algorithm computes them by the
recurrence
$$\alpha_1 = a_1, \qquad \beta_i = \frac{b_i}{\alpha_{i-1}}, \qquad \alpha_i = a_i - \beta_i c_{i-1}
  \qquad (i = 2, \ldots, n)$$
of (3.53). The module states this recurrence, the bidiagonal substitutions (3.54)–(3.55), the
stability of the algorithm in floating-point arithmetic (Section 3.7.1), and the division-free
variant (3.56) of Section 3.7.2.

The proofs specialize the backbone modules `Numlib.LinearAlgebra.Matrix.LU` (band preservation
`Matrix.IsLU.hasLowerBandwidth` and `Matrix.IsLU.hasUpperBandwidth`, the tridiagonal matrix
`Matrix.tridiagonalOfNat`, the Thomas recurrences `Matrix.thomasAlpha`, `Matrix.thomasBeta`,
`Matrix.thomasGamma` and the factors `Matrix.thomasLower`, `Matrix.thomasUpper`),
`Numlib.LinearAlgebra.Matrix.Band` (the bandwidths), `Numlib.Direct.Substitution`, and
`Numlib.FloatingPoint.LU` (the rounding-error analysis of the Thomas algorithm,
`FloatingPoint.RoundsThomas`).

## Main results

* Property 3.4, `QuarteroniSaccoSaleri.Chapter03.property_3_4_lower`: if $A$ has lower bandwidth $p$
  and a unique LU factorization, then $L$ has lower bandwidth $p$.
* Property 3.4, `QuarteroniSaccoSaleri.Chapter03.property_3_4_upper`: if $A$ has upper bandwidth
  $q$, then $U$ has upper bandwidth $q$.
* (3.53), `QuarteroniSaccoSaleri.Chapter03.equation_3_53`: the Thomas algorithm gives the LU
  factorization of a tridiagonal matrix.
* (3.54), `QuarteroniSaccoSaleri.Chapter03.equation_3_54`: the forward substitution for the
  bidiagonal factor $L$.
* (3.55), `QuarteroniSaccoSaleri.Chapter03.equation_3_55`: the backward substitution for the
  bidiagonal factor $U$, which solves the tridiagonal system.
* Section 3.7.1, `QuarteroniSaccoSaleri.Chapter03.thomas_backward_error`: the computed factors
  satisfy $\hat L \hat U = A + \delta A$ with $|\delta A| \le (4u + 3u^2 + u^3)|\hat L||\hat U|$.
* Section 3.7.1, `QuarteroniSaccoSaleri.Chapter03.thomas_backward_error_posDef`: under the sign
  pattern of the symmetric positive definite and M-matrix cases, $|\delta A| \le \frac{4u + 3u^2 +
  u^3}{1 - u}|A|$.
* (3.56), `QuarteroniSaccoSaleri.Chapter03.equation_3_56`: the Thomas algorithm without divisions.

## Conventions

* "$A$ has lower bandwidth $p$" is the condition $a_{ij} = 0$ for $i > j + p$ of Section 1.6.3 of
  the book, and "upper bandwidth $q$" is $a_{ij} = 0$ for $j > i + q$. On `Fin n` these are the
  predicates `Matrix.HasLowerBandwidth` and `Matrix.HasUpperBandwidth`
  (`Matrix.hasLowerBandwidth_iff_fin`).
* The tridiagonal matrix of Section 3.7.1 with diagonal $a$, subdiagonal $b$ and superdiagonal $c$
  is `Matrix.tridiagonalOfNat a b c n` for sequences `a b c : ℕ → ℝ`. Indices are $0$-based: $a_i$
  is at $(i, i)$, $b_i$ at $(i, i - 1)$ and $c_i$ at $(i, i + 1)$. So the book's $a_i$, $b_i$, $c_i$
  are `a (i - 1)`, `b (i - 1)`, `c (i - 1)`, and the Thomas coefficients $\alpha_i$, $\beta_i$,
  $\gamma_i$ are `Matrix.thomasAlpha a b c (i - 1)` and so on.
* The bidiagonal factors are `Matrix.thomasLower a b c n`, unit lower with subdiagonal $\beta$, and
  `Matrix.thomasUpper a b c n`, with diagonal $\alpha$ and superdiagonal $c$.
* The computed Thomas coefficients $\hat\alpha$, $\hat\beta$ are an admissible
  `FloatingPoint.RoundsThomas m a b c α̂ β̂` of the relational rounding model: the recurrence (3.53)
  with its three roundings per step. The computed factors are the bidiagonal matrices
  `Matrix.lowerBidiagonalOf β̂ n` and `Matrix.upperBidiagonalOf α̂ c n`.

## Deviations from the source

* **Property 3.4** (correction). The source assumes only that an LU factorization of $A$ exists. The
  statement on $L$ is false without uniqueness, and it is stated under the hypothesis of Theorem
  3.4. See `QuarteroniSaccoSaleri.Chapter03.property_3_4_lower`.
* **Section 3.7.1, stability of the Thomas algorithm** (reading). The source quotes the constants
  $4u + 3u^2 + u^3$ and $(4u + 3u^2 + u^3)/(1 - u)$ from [higham2002accuracy]. They are stated for
  $u < 1/2$ and for $u \le 1/4$, respectively, and the condition "for $u$ small enough" of the
  second bound is read as a sign condition on the computed factors. See
  `QuarteroniSaccoSaleri.Chapter03.thomas_backward_error` and
  `QuarteroniSaccoSaleri.Chapter03.thomas_backward_error_posDef`.

## Not formalized

* **The banded storage format.**
* **Programs 10–13.**
* **The operation counts.**
-/

open Finset Matrix

namespace QuarteroniSaccoSaleri.Chapter03

variable {n : ℕ}

/-! ### Property 3.4: band preservation -/

/-- **Property 3.4** of [quarteroni2000numerical], the lower factor. Let
$A \in \mathbb{R}^{n \times n}$ have the LU factorization $A = LU$, and assume that the leading
principal submatrices of $A$ of orders $1, \ldots, n - 1$ are nonsingular, so that this
factorization is unique. If $A$ has lower bandwidth $p$, that is, $a_{ij} = 0$ for $i > j + p$,
then $l_{ij} = 0$ for $i > j + p$.

**Correction.** The source assumes only that an LU factorization of $A$ exists. Without
uniqueness the statement is false: the matrix $D = L_\beta U_\beta$ of Example 3.3 has lower
bandwidth $0$, while $L_\beta$ does not for $\beta \neq 0$ (see
`QuarteroniSaccoSaleri.Chapter03.example_3_3_d`). The theorem adds the hypothesis of Theorem
3.4, under which the factorization is unique.

The hypothesis is stated for the strict leading principal submatrices of orders
$0, \ldots, n - 1$, as in `QuarteroniSaccoSaleri.Chapter03.theorem_3_4`. The proof uses
`Matrix.IsLU.hasLowerBandwidth`. -/
theorem property_3_4_lower {A L U : Matrix (Fin n) (Fin n) ℝ} (h : IsLU A L U)
    (hA : ∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k)) {p : ℕ}
    (hp : ∀ i j : Fin n, (j : ℕ) + p < i → A i j = 0) :
    ∀ i j : Fin n, (j : ℕ) + p < i → L i j = 0 :=
  hasLowerBandwidth_iff_fin.1 (h.hasLowerBandwidth hA (hasLowerBandwidth_iff_fin.2 hp))

/-- **Property 3.4** of [quarteroni2000numerical], the upper factor. Let
$A \in \mathbb{R}^{n \times n}$, and let $A = LU$ be an LU factorization with $L$ unit lower
triangular. If $A$ has upper bandwidth $q$, that is, $a_{ij} = 0$ for $j > i + q$, then
$u_{ij} = 0$ for $j > i + q$.

This part holds for every LU factorization; no uniqueness is needed. The proof uses
`Matrix.IsLU.hasUpperBandwidth`. -/
theorem property_3_4_upper {A L U : Matrix (Fin n) (Fin n) ℝ} (h : IsLU A L U) {q : ℕ}
    (hq : ∀ i j : Fin n, (i : ℕ) + q < j → A i j = 0) :
    ∀ i j : Fin n, (i : ℕ) + q < j → U i j = 0 :=
  hasUpperBandwidth_iff_fin.1 (h.hasUpperBandwidth (hasUpperBandwidth_iff_fin.2 hq))

/-! ### §3.7.1: tridiagonal matrices and the Thomas algorithm -/

section Thomas

variable (a b c : ℕ → ℝ)

/-- **Equation (3.53)** of [quarteroni2000numerical] (the Thomas algorithm). Let
$A \in \mathbb{R}^{n \times n}$ be the tridiagonal matrix with diagonal $a$, subdiagonal $b$ and
superdiagonal $c$. The coefficients of the Thomas algorithm satisfy
$$\alpha_0 = a_0, \qquad \beta_{i+1} = \frac{b_{i+1}}{\alpha_i}, \qquad \alpha_{i+1} = a_{i+1} -
  \beta_{i+1} c_i.$$
Let $L$ be the unit lower bidiagonal matrix with subdiagonal entries $l_{i+1,i} = \beta_{i+1}$,
and let $U$ be the upper bidiagonal matrix with diagonal entries $u_{ii} = \alpha_i$ and
superdiagonal entries $u_{i,i+1} = c_i$. If the pivots $\alpha_i$ are nonzero for
$i = 0, \ldots, n - 2$, then $A = LU$ is the LU factorization of $A$, that is, the Doolittle
factorization.

The indices are $0$-based; the book writes $\alpha_1 = a_1$ and $i = 2, \ldots, n$. The
coefficients are `Matrix.thomasAlpha` and `Matrix.thomasBeta`. The proof uses
`Matrix.isLU_tridiagonal_thomas`. -/
theorem equation_3_53 (hα : ∀ i, i + 1 < n → thomasAlpha a b c i ≠ 0) :
    thomasAlpha a b c 0 = a 0 ∧
    (∀ i, thomasBeta a b c (i + 1) = b (i + 1) / thomasAlpha a b c i) ∧
    (∀ i, thomasAlpha a b c (i + 1) = a (i + 1) - thomasBeta a b c (i + 1) * c i) ∧
    (∀ i j : Fin n, thomasLower a b c n i j =
      if i = j then 1 else if (j : ℕ) + 1 = i then thomasBeta a b c i else 0) ∧
    (∀ i j : Fin n, thomasUpper a b c n i j =
      if i = j then thomasAlpha a b c i else if (i : ℕ) + 1 = j then c i else 0) ∧
    IsLU (tridiagonalOfNat a b c n) (thomasLower a b c n) (thomasUpper a b c n) :=
  ⟨thomasAlpha_zero a b c, thomasBeta_succ a b c, thomasAlpha_succ a b c, fun _ _ => rfl,
    fun _ _ => rfl, isLU_tridiagonal_thomas a b c hα⟩

/-- Forward substitution on a unit lower bidiagonal matrix: the sum over $j < i + 1$ has the single
term $j = i$. -/
private theorem sum_filter_lt_succ_eq {L : Matrix (Fin n) (Fin n) ℝ}
    (hL : ∀ i j : Fin n, j < i → (j : ℕ) + 1 ≠ i → L i j = 0) (y : Fin n → ℝ) {i : Fin n}
    (hi : (i : ℕ) + 1 < n) :
    ∑ j ∈ univ.filter (fun j : Fin n => j < ⟨i + 1, hi⟩), L ⟨i + 1, hi⟩ j * y j =
      L ⟨i + 1, hi⟩ i * y i := by
  refine Finset.sum_eq_single i (fun j hj hji => ?_)
    (fun h => (h (mem_filter.2 ⟨mem_univ _, Fin.lt_def.2 (Nat.lt_succ_self _)⟩)).elim)
  rw [hL _ _ (mem_filter.1 hj).2 fun h => hji (Fin.ext (Nat.succ_injective h)), zero_mul]

/-- Backward substitution on an upper bidiagonal matrix: the sum over $j > i$ has the single term
$j = i + 1$. -/
private theorem sum_filter_gt_eq {U : Matrix (Fin n) (Fin n) ℝ}
    (hU : ∀ i j : Fin n, i < j → (i : ℕ) + 1 ≠ j → U i j = 0) (y : Fin n → ℝ) {i : Fin n}
    (hi : (i : ℕ) + 1 < n) :
    ∑ j ∈ univ.filter (fun j : Fin n => i < j), U i j * y j =
      U i ⟨i + 1, hi⟩ * y ⟨i + 1, hi⟩ := by
  refine Finset.sum_eq_single (⟨i + 1, hi⟩ : Fin n) (fun j hj hji => ?_)
    (fun h => (h (mem_filter.2 ⟨mem_univ _, Fin.lt_def.2 (Nat.lt_succ_self _)⟩)).elim)
  rw [hU _ _ (mem_filter.1 hj).2 fun h => hji (Fin.ext h.symm), zero_mul]

/-- **Equation (3.54)** of [quarteroni2000numerical], the bidiagonal forward substitution. Let $L$
be the unit lower bidiagonal factor of (3.53), and let $f \in \mathbb{R}^n$. The solution $y$ of
$Ly = f$ by forward substitution satisfies
$$y_0 = f_0, \qquad y_{i+1} = f_{i+1} - \beta_{i+1} y_i \quad (i = 0, \ldots, n - 2).$$

The indices are $0$-based; the book writes $y_1 = f_1$ and $y_i = f_i - \beta_i y_{i-1}$ for
$i = 2, \ldots, n$. The solution is `Matrix.forwardSubst L f`. -/
theorem equation_3_54 (f : Fin n → ℝ) :
    (∀ h0 : 0 < n, forwardSubst (thomasLower a b c n) f ⟨0, h0⟩ = f ⟨0, h0⟩) ∧
    ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n),
      forwardSubst (thomasLower a b c n) f ⟨i + 1, hi⟩ =
        f ⟨i + 1, hi⟩ - thomasBeta a b c (i + 1) * forwardSubst (thomasLower a b c n) f i := by
  have hL : ∀ i j : Fin n, j < i → (j : ℕ) + 1 ≠ i → thomasLower a b c n i j = 0 := by
    intro i j hji hne
    simp [thomasLower, hji.ne', hne]
  constructor
  · intro h0
    rw [forwardSubst_apply, Finset.sum_eq_zero fun j hj =>
      absurd (mem_filter.1 hj).2 (not_lt.2 (Fin.le_def.2 (Nat.zero_le _))), sub_zero]
    simp [thomasLower]
  · intro i hi
    have hne : (⟨i + 1, hi⟩ : Fin n) ≠ i := fun h => by simp [Fin.ext_iff] at h
    rw [forwardSubst_apply, sum_filter_lt_succ_eq hL _ hi]
    simp [thomasLower, hne]

/-- **Equation (3.55)** of [quarteroni2000numerical], the bidiagonal backward substitution. Let $L$
and $U$ be the bidiagonal factors of (3.53) of the tridiagonal matrix $A$, and let
$y, f \in \mathbb{R}^n$. The solution $x$ of $Ux = y$ by backward substitution satisfies
$$x_{n-1} = \frac{y_{n-1}}{\alpha_{n-1}}, \qquad x_i = \frac{y_i - c_i x_{i+1}}{\alpha_i} \quad
  (i = n - 2, \ldots, 0).$$
If all pivots $\alpha_i$, $i = 0, \ldots, n - 1$, are nonzero, then the forward substitution
(3.54) followed by this backward substitution solves the tridiagonal system $Ax = f$.

The indices are $0$-based; the book writes $x_n = y_n/\alpha_n$ and $i = n - 1, \ldots, 1$. The
solution is `Matrix.backSubst U y`. The proof of the last statement uses
`Matrix.mulVec_luSolve`. -/
theorem equation_3_55 (y f : Fin n → ℝ) :
    (∀ h0 : 0 < n, backSubst (thomasUpper a b c n) y ⟨n - 1, Nat.sub_one_lt h0.ne'⟩ =
      y ⟨n - 1, Nat.sub_one_lt h0.ne'⟩ / thomasAlpha a b c (n - 1)) ∧
    (∀ (i : Fin n) (hi : (i : ℕ) + 1 < n),
      backSubst (thomasUpper a b c n) y i =
        (y i - c i * backSubst (thomasUpper a b c n) y ⟨i + 1, hi⟩) / thomasAlpha a b c i) ∧
    ((∀ i, i < n → thomasAlpha a b c i ≠ 0) →
      tridiagonalOfNat a b c n *ᵥ
        backSubst (thomasUpper a b c n) (forwardSubst (thomasLower a b c n) f) = f) := by
  have hU : ∀ i j : Fin n, i < j → (i : ℕ) + 1 ≠ j → thomasUpper a b c n i j = 0 := by
    intro i j hij hne
    simp [thomasUpper, hij.ne, hne]
  refine ⟨fun h0 => ?_, fun i hi => ?_, fun hα => ?_⟩
  · rw [backSubst_apply, Finset.sum_eq_zero fun j hj => absurd (mem_filter.1 hj).2
      (not_lt.2 (Fin.le_def.2 (Nat.le_sub_one_of_lt j.2))), sub_zero]
    simp [thomasUpper]
  · have hne : i ≠ (⟨i + 1, hi⟩ : Fin n) := fun h => by simp [Fin.ext_iff] at h
    rw [backSubst_apply, sum_filter_gt_eq hU _ hi]
    simp [thomasUpper, hne]
  · exact mulVec_luSolve f (isLU_tridiagonal_thomas a b c fun i hi => hα i (Nat.lt_of_succ_lt hi))
      fun i => by simpa [thomasUpper] using hα i i.2

open FloatingPoint in
/-- **Section 3.7.1** of [quarteroni2000numerical], stability of the Thomas algorithm. Let $A$ be
the tridiagonal matrix with diagonal $a$, subdiagonal $b$ and superdiagonal $c$, and let
$u < 1/2$ be the unit roundoff of a rounding model. Let $\hat\alpha$, $\hat\beta$ be the
coefficients that (3.53) computes in floating-point arithmetic, with all computed pivots
$\hat\alpha_i$ nonzero, and let $\hat L$, $\hat U$ be the bidiagonal factors made from them.
Then there is a matrix $\delta A$ with
$$\hat L \hat U = A + \delta A, \qquad |\delta A| \le (4u + 3u^2 + u^3) |\hat L| |\hat U|,$$
where the absolute values and the inequality are entrywise.

**Reading.** The source quotes this bound from (9.20) of [higham2002accuracy]. The backbone
proves it with the constant $u/(1 - u)$ of the relational model, which is smaller than
$4u + 3u^2 + u^3$ when $u < 1/2$. So the theorem adds the hypothesis $u < 1/2$.

The source speaks of a nonsingular matrix $A$; the theorem does not need this. The coefficients
are sequences indexed by $\mathbb{N}$, and the hypothesis $\hat\alpha_i \neq 0$ is stated for
every $i \in \mathbb{N}$. The computed coefficients are an admissible
`FloatingPoint.RoundsThomas m a b c α β`, and $\hat L$, $\hat U$ are
`Matrix.lowerBidiagonalOf β n` and `Matrix.upperBidiagonalOf α c n`. The proof uses
`FloatingPoint.exists_roundsThomas_mul_eq_add`. -/
theorem thomas_backward_error {m : RoundingModel ℝ} (hu : 2 * m.u < 1) {α β : ℕ → ℝ}
    (h : RoundsThomas m a b c α β) (hα : ∀ i, α i ≠ 0) :
    ∃ δA : Matrix (Fin n) (Fin n) ℝ,
      δA.abs ≤ₑ (4 * m.u + 3 * m.u ^ 2 + m.u ^ 3) •
          ((lowerBidiagonalOf β n).abs * (upperBidiagonalOf α c n).abs) ∧
        lowerBidiagonalOf β n * upperBidiagonalOf α c n = tridiagonalOfNat a b c n + δA := by
  have hu0 := m.u_nonneg
  have hu1 : m.u < 1 := by linarith
  obtain ⟨δA, hδA, hLU⟩ := exists_roundsThomas_mul_eq_add hu1 h hα n
  refine ⟨δA, hδA.trans fun i j => ?_, hLU⟩
  rw [gamma_one_eq]
  have hM : 0 ≤ ((lowerBidiagonalOf β n).abs * (upperBidiagonalOf α c n).abs) i j := by
    rw [Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  refine mul_le_mul_of_nonneg_right ?_ hM
  rw [div_le_iff₀ (by linarith)]
  have h1 : 0 ≤ m.u * (1 - 2 * m.u) := mul_nonneg hu0 (by linarith)
  have h2 : 0 ≤ m.u ^ 2 * (1 - 2 * m.u) := mul_nonneg (sq_nonneg _) (by linarith)
  have h3 : 0 ≤ m.u ^ 3 * (1 - 2 * m.u) := mul_nonneg (pow_nonneg hu0 3) (by linarith)
  nlinarith

open FloatingPoint in
/-- **Section 3.7.1** of [quarteroni2000numerical], the symmetric positive definite and M-matrix
cases. Let $A$ be the tridiagonal matrix with diagonal $a$, subdiagonal $b$ and superdiagonal
$c$, and let $u \le 1/4$ be the unit roundoff of a rounding model. Let $\hat\alpha$, $\hat\beta$
be the coefficients that (3.53) computes in floating-point arithmetic, with $\hat\alpha_i > 0$
and $\hat\beta_{i+1} c_i \ge 0$ for all $i$, and let $\hat L$, $\hat U$ be the bidiagonal
factors made from them. Then there is a matrix $\delta A$ with
$$\hat L \hat U = A + \delta A, \qquad |\delta A| \le \frac{4u + 3u^2 + u^3}{1 - u} |A|$$
entrywise. This expresses the stability of the factorization.

**Reading.** The source states this bound for symmetric positive definite matrices and
M-matrices, "for $u$ small enough". The theorem reads this as the hypothesis that the computed
pivots are positive and the products $\hat\beta_{i+1} c_i$ are nonnegative, the sign pattern of
the exact factors of such matrices. The source quotes the bound from Theorem 9.14 of
[higham2002accuracy]. The backbone proves it with the constant $u/(1 - 2u)$, which is smaller
than the constant of the source when $u \le 1/4$, so the theorem adds this hypothesis.

The proof uses `FloatingPoint.exists_roundsThomas_mul_eq_add_of_diag_pos`. -/
theorem thomas_backward_error_posDef {m : RoundingModel ℝ} (hu : 4 * m.u ≤ 1) {α β : ℕ → ℝ}
    (h : RoundsThomas m a b c α β) (hα : ∀ i, 0 < α i) (hbc : ∀ i, 0 ≤ β (i + 1) * c i) :
    ∃ δA : Matrix (Fin n) (Fin n) ℝ,
      δA.abs ≤ₑ ((4 * m.u + 3 * m.u ^ 2 + m.u ^ 3) / (1 - m.u)) • (tridiagonalOfNat a b c n).abs ∧
        lowerBidiagonalOf β n * upperBidiagonalOf α c n = tridiagonalOfNat a b c n + δA := by
  have hu0 := m.u_nonneg
  have hu2 : 2 * m.u < 1 := by linarith
  obtain ⟨δA, hδA, hLU⟩ := exists_roundsThomas_mul_eq_add_of_diag_pos hu2 h hα hbc n
  refine ⟨δA, hδA.trans fun i j => ?_, hLU⟩
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  have h1 : 0 ≤ m.u * (1 - 4 * m.u) := mul_nonneg hu0 (by linarith)
  have h2 : 0 ≤ m.u ^ 2 * (1 - 4 * m.u) := mul_nonneg (sq_nonneg _) (by linarith)
  have h3 : 0 ≤ m.u ^ 3 := pow_nonneg hu0 3
  nlinarith

/-- **Equation (3.56)** of [quarteroni2000numerical], Section 3.7.2, the Thomas algorithm without
divisions. Let $A$ be the tridiagonal matrix with diagonal $a$, subdiagonal $b$ and
superdiagonal $c$, and assume that the pivots $\alpha_i$ of (3.53) are nonzero for
$i = 0, \ldots, n - 1$. Let the reciprocal pivots be
$$\gamma_0 = a_0^{-1}, \qquad \gamma_{i+1} = (a_{i+1} - b_{i+1} \gamma_i c_i)^{-1},$$
so that $\gamma_i = \alpha_i^{-1}$. Let $L$ be the lower bidiagonal matrix with diagonal
$\gamma_i^{-1}$ and subdiagonal $b$, let $D = \operatorname{diag}(\gamma_i)$, and let $M^T$ be
the upper bidiagonal matrix with diagonal $\gamma_i^{-1}$ and superdiagonal $c$. Then
$A = LDM^T$. For every $f, y \in \mathbb{R}^n$, the forward substitution for $Ly = f$ reads
$$y_0 = \gamma_0 f_0, \qquad y_{i+1} = \gamma_{i+1} (f_{i+1} - b_{i+1} y_i),$$
and the backward substitution for $(DM^T)x = y$ reads
$$x_{n-1} = y_{n-1}, \qquad x_i = y_i - \gamma_i c_i x_{i+1}.$$
Neither substitution divides.

The indices are $0$-based. The book starts the recurrence at $\gamma_0 = 0$ with $b_1 = 0$ and
$c_n = 0$, which gives the same $\gamma_1 = a_1^{-1}$. The identity $\gamma_i = \alpha_i^{-1}$
holds for every $i$, with Lean's convention $0^{-1} = 0$. The reciprocal pivots are
`Matrix.thomasGamma`. -/
theorem equation_3_56 (hα : ∀ i, i < n → thomasAlpha a b c i ≠ 0) (f y : Fin n → ℝ) :
    (∀ i, thomasGamma a b c i = (thomasAlpha a b c i)⁻¹) ∧
    thomasGamma a b c 0 = (a 0)⁻¹ ∧
    (∀ i, thomasGamma a b c (i + 1) = (a (i + 1) - b (i + 1) * thomasGamma a b c i * c i)⁻¹) ∧
    tridiagonalOfNat a b c n =
      (of fun i j : Fin n =>
          if i = j then (thomasGamma a b c i)⁻¹ else if (j : ℕ) + 1 = i then b i else 0) *
        diagonal (fun i : Fin n => thomasGamma a b c i) *
        of (fun i j : Fin n =>
          if i = j then (thomasGamma a b c i)⁻¹ else if (i : ℕ) + 1 = j then c i else 0) ∧
    (∀ h0 : 0 < n,
      forwardSubst (of fun i j : Fin n =>
          if i = j then (thomasGamma a b c i)⁻¹ else if (j : ℕ) + 1 = i then b i else 0) f
        ⟨0, h0⟩ = thomasGamma a b c 0 * f ⟨0, h0⟩) ∧
    (∀ (i : Fin n) (hi : (i : ℕ) + 1 < n),
      forwardSubst (of fun i j : Fin n =>
          if i = j then (thomasGamma a b c i)⁻¹ else if (j : ℕ) + 1 = i then b i else 0) f
        ⟨i + 1, hi⟩ = thomasGamma a b c (i + 1) * (f ⟨i + 1, hi⟩ - b (i + 1) *
          forwardSubst (of fun i j : Fin n =>
            if i = j then (thomasGamma a b c i)⁻¹ else if (j : ℕ) + 1 = i then b i else 0) f i)) ∧
    (∀ h0 : 0 < n,
      backSubst (diagonal (fun i : Fin n => thomasGamma a b c i) * of (fun i j : Fin n =>
          if i = j then (thomasGamma a b c i)⁻¹ else if (i : ℕ) + 1 = j then c i else 0)) y
        ⟨n - 1, Nat.sub_one_lt h0.ne'⟩ = y ⟨n - 1, Nat.sub_one_lt h0.ne'⟩) ∧
    ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n),
      backSubst (diagonal (fun i : Fin n => thomasGamma a b c i) * of (fun i j : Fin n =>
          if i = j then (thomasGamma a b c i)⁻¹ else if (i : ℕ) + 1 = j then c i else 0)) y i =
        y i - thomasGamma a b c i * c i *
          backSubst (diagonal (fun i : Fin n => thomasGamma a b c i) * of (fun i j : Fin n =>
            if i = j then (thomasGamma a b c i)⁻¹ else if (i : ℕ) + 1 = j then c i else 0)) y
            ⟨i + 1, hi⟩ := by
  have hγ : ∀ i, thomasGamma a b c i = (thomasAlpha a b c i)⁻¹ :=
    thomasGamma_eq_inv_thomasAlpha a b c
  have hγne : ∀ i : Fin n, thomasGamma a b c i ≠ 0 := fun i => by
    rw [hγ]; exact inv_ne_zero (hα i i.2)
  set Lγ : Matrix (Fin n) (Fin n) ℝ := of fun i j =>
    if i = j then (thomasGamma a b c i)⁻¹ else if (j : ℕ) + 1 = i then b i else 0 with hLγ
  set Mγ : Matrix (Fin n) (Fin n) ℝ := of fun i j =>
    if i = j then (thomasGamma a b c i)⁻¹ else if (i : ℕ) + 1 = j then c i else 0 with hMγ
  set Dγ : Matrix (Fin n) (Fin n) ℝ := diagonal fun i : Fin n => thomasGamma a b c i with hDγ
  -- `Lγ = L diag(α)`, `Mγ = U`, `Dγ = diag(α⁻¹)`
  have hLγ' : Lγ = thomasLower a b c n * diagonal (fun i : Fin n => thomasAlpha a b c i) := by
    ext i j
    rw [mul_diagonal, hLγ, of_apply, thomasLower, of_apply, hγ, inv_inv]
    split_ifs with h1 h2
    · rw [h1, one_mul]
    · obtain ⟨i, hi⟩ := i
      obtain rfl : i = j + 1 := h2.symm
      rw [thomasBeta_succ, div_mul_cancel₀ _ (hα j (by omega))]
    · rw [zero_mul]
  have hMγ' : Mγ = thomasUpper a b c n := by
    ext i j
    rw [hMγ, of_apply, thomasUpper, of_apply, hγ, inv_inv]
  have hfact : tridiagonalOfNat a b c n = Lγ * Dγ * Mγ := by
    have hD1 : diagonal (fun i : Fin n => thomasAlpha a b c i) * Dγ = 1 := by
      rw [hDγ, diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      rw [hγ, mul_inv_cancel₀ (hα i i.2)]
    rw [hLγ', hMγ', Matrix.mul_assoc (thomasLower a b c n), hD1, Matrix.mul_one,
      (isLU_tridiagonal_thomas a b c fun i hi => hα i (Nat.lt_of_succ_lt hi)).mul_eq]
  have hDM : Dγ * Mγ = of fun i j : Fin n =>
      if i = j then 1 else if (i : ℕ) + 1 = j then thomasGamma a b c i * c i else 0 := by
    ext i j
    rw [hDγ, diagonal_mul, hMγ, of_apply, of_apply]
    split_ifs with h1
    · exact mul_inv_cancel₀ (hγne i)
    · rfl
    · exact mul_zero _
  have hL0 : ∀ i j : Fin n, j < i → (j : ℕ) + 1 ≠ i → Lγ i j = 0 := by
    intro i j hji hne
    simp [hLγ, hji.ne', hne]
  have hU0 : ∀ i j : Fin n, i < j → (i : ℕ) + 1 ≠ j → (Dγ * Mγ) i j = 0 := by
    intro i j hij hne
    rw [hDM]
    simp [hij.ne, hne]
  refine ⟨hγ, rfl, fun i => rfl, hfact, fun h0 => ?_, fun i hi => ?_, fun h0 => ?_, fun i hi => ?_⟩
  · rw [forwardSubst_apply, Finset.sum_eq_zero fun j hj =>
      absurd (mem_filter.1 hj).2 (not_lt.2 (Fin.le_def.2 (Nat.zero_le _))), sub_zero]
    simp [hLγ, div_eq_mul_inv, mul_comm]
  · have hne : (⟨i + 1, hi⟩ : Fin n) ≠ i := fun h => by simp [Fin.ext_iff] at h
    rw [forwardSubst_apply, sum_filter_lt_succ_eq hL0 _ hi]
    simp [hLγ, hne, div_eq_mul_inv, mul_comm]
  · rw [backSubst_apply, Finset.sum_eq_zero fun j hj => absurd (mem_filter.1 hj).2
      (not_lt.2 (Fin.le_def.2 (Nat.le_sub_one_of_lt j.2))), sub_zero, hDM]
    simp
  · have hne : i ≠ (⟨i + 1, hi⟩ : Fin n) := fun h => by simp [Fin.ext_iff] at h
    rw [backSubst_apply, sum_filter_gt_eq hU0 _ hi, hDM]
    simp [hne]

end Thomas

end QuarteroniSaccoSaleri.Chapter03
