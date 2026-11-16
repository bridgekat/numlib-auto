/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.FloatingPoint.Substitution
import NumlibSurface.QuarteroniSaccoSaleri.Chapter03.Section01

/-!
# Quarteroni, Sacco and Saleri, Section 3.2: Solution of Triangular Systems

This module formalizes Section 3.2 of [quarteroni2000numerical]. Forward substitution (3.22) solves
$Lx = b$ for a nonsingular lower triangular $L \in \mathbb{R}^{n \times n}$ by $x_1 = b_1 / l_{11}$
and $x_i = (b_i - \sum_{j < i} l_{ij} x_j) / l_{ii}$, and backward substitution (3.23) solves
$Ux = b$ for a nonsingular upper triangular $U$ in the same way from the last index. Section 3.2.2
analyses the rounding errors: the computed solution $\hat{x}$ solves a perturbed system
$(T + \delta T) \hat{x} = b$ with $|\delta T| \le \gamma_n |T|$, $\gamma_n = nu / (1 - nu)$ (3.24),
which gives the relative error bound (3.25), and componentwise bounds hold for matrices with
dominant diagonal entries. Section 3.2.3 computes the inverse of an upper triangular matrix column
by column (3.26), by its leading blocks (3.27), and by a recurrence on the entries (3.28).

The proofs specialize the backbone modules `Numlib.Direct.Substitution` (forward and backward
substitution as total functions on a finite linear order, their correctness, and the inverse of a
triangular matrix column by column, block by block and by the recurrence on the entries) and
`Numlib.FloatingPoint.Substitution` (the rounding error analysis of substitution in the relational
rounding model, after Theorems 8.5 and 8.7 and Lemma 8.8 of [higham2002accuracy]).

## Main results

* Equation (3.22), `QuarteroniSaccoSaleri.Chapter03.equation_3_22`: forward substitution solves
  $Lx = b$.
* Equation (3.23), `QuarteroniSaccoSaleri.Chapter03.equation_3_23`: backward substitution solves
  $Ux = b$.
* Equation (3.24), `QuarteroniSaccoSaleri.Chapter03.equation_3_24`: the computed solution solves
  $(T + \delta T) \hat{x} = b$ with $|\delta T| \le \gamma_n |T|$.
* Equation (3.25), `QuarteroniSaccoSaleri.Chapter03.equation_3_25`: $\|x - \hat{x}\|_\infty /
  \|x\|_\infty \le \gamma_n K_\infty(T) / (1 - \gamma_n K_\infty(T))$.
* Section 3.2.2, `QuarteroniSaccoSaleri.Chapter03.backSubst_componentwise_error`: the componentwise
  bound $2^{n-i+1} \gamma_n \max_{j \ge i} |\hat{x}_j|$ when $|u_{ij}| \le |u_{ii}|$.
* Section 3.2.2, `QuarteroniSaccoSaleri.Chapter03.backSubst_error_of_diagDominant`: the bound
  $(2n - 1) \gamma_n \|\hat{x}\|_\infty$ for a diagonally dominant $U$.
* Equation (3.26), `QuarteroniSaccoSaleri.Chapter03.equation_3_26`: the columns of $U^{-1}$ are
  computed by backward substitution.
* Equation (3.27), `QuarteroniSaccoSaleri.Chapter03.equation_3_27`: the leading part of the $k$-th
  column of $U^{-1}$ solves a system with the leading principal submatrix of order $k$.
* Equation (3.28), `QuarteroniSaccoSaleri.Chapter03.equation_3_28`: the recurrence for the entries
  of $U^{-1}$.

## Conventions

* Forward substitution (3.22) is `Matrix.forwardSubst L b`, and backward substitution (3.23) is
  `Matrix.backSubst U b`. The recurrences of the book are the theorems
  `QuarteroniSaccoSaleri.Chapter03.equation_3_22` and
  `QuarteroniSaccoSaleri.Chapter03.equation_3_23`.
* "$L$ is nonsingular lower triangular" is `L.IsLowerTriangular` together with `IsUnit L`. For a
  triangular matrix this is the same as a diagonal without zeros
  (`Matrix.IsLowerTriangular.isUnit_iff`).
* Indices start at $0$. Under `[NeZero n]`, the first and the last index of `Fin n` are `0` and `⊤`
  (`Fin.last`).
* A solution $\hat{x}$ of $Tx = b$ computed by substitution in floating-point arithmetic with unit
  roundoff $u$ is an admissible `FloatingPoint.RoundsForwardSubst m T b xhat` (or
  `FloatingPoint.RoundsBackSubst m T b xhat`) of the relational rounding model
  `m : FloatingPoint.RoundingModel ℝ` of `Numlib.FloatingPoint.Model`. The number `m.u` is the unit
  roundoff $u = \frac{1}{2} \beta^{1-t}$ of the book. Every product is rounded, the products are
  subtracted from $b_i$ one at a time in any order with one rounding each, and the division by the
  diagonal entry is rounded. This is the order of Program 2, with running differences, for which the
  constant of (3.24) is exactly $nu / (1 - nu)$.
* The constant $\gamma_n = nu / (1 - nu)$ is the backbone's `FloatingPoint.gamma m.u n`, and (3.25)
  uses the $\infty$-norms of Section 3.1.

## Deviations from the source

* **Equation (3.25)** (correction). The book prints $nu$ where the constant that (3.24) and Theorem
  3.1 give is $\gamma_n = nu / (1 - nu) = nu + O(u^2)$. The statement uses $\gamma_n$. See
  `QuarteroniSaccoSaleri.Chapter03.equation_3_25`.
* **Section 3.2.2, the diagonally dominant case** (reading). The sentence "the same result holds …
  if $L$ and $U$ are diagonally dominant" suggests the bound $2^{n-i+1} \gamma_n$. The statement is
  the linear bound $(2n - 1) \gamma_n \|\hat{x}\|_\infty$ that holds under diagonal dominance by
  rows. See `QuarteroniSaccoSaleri.Chapter03.backSubst_error_of_diagDominant`.
* **Equation (3.27)** (typo). The book describes $l_k$ as the vector of $\mathbb{R}^k$ whose first
  entry is $1$. The $1$ is in the last ($k$-th) position. See
  `QuarteroniSaccoSaleri.Chapter03.equation_3_27`.

## Not formalized

* **Programs 1–3.** They implement `Matrix.forwardSubst` and `Matrix.backSubst`.
* **The operation counts of substitution.**
* **Equation (3.25) in the $1$-norm and the Frobenius norm.**
-/

open Finset Matrix

namespace QuarteroniSaccoSaleri.Chapter03

variable {n : ℕ}

/-! ### Forward and backward substitution, (3.22)–(3.23) -/

/-- **Equation (3.22)** of [quarteroni2000numerical], forward substitution. Let $n \ge 1$, let
$L \in \mathbb{R}^{n \times n}$ be nonsingular and lower triangular, and let
$b \in \mathbb{R}^n$. The vector $x$ computed by forward substitution satisfies
$$x_1 = \frac{b_1}{l_{11}}, \qquad x_i = \frac{1}{l_{ii}} \Bigl( b_i - \sum_{j < i} l_{ij} x_j
  \Bigr), \quad i = 2, \dots, n,$$
and it solves $Lx = b$.

The vector $x$ is `Matrix.forwardSubst L b`, and its first index is `0`. The recurrence is
stated for every $i$, including the first index, where the sum is empty. The proof is the
backbone's `Matrix.forwardSubst_apply` and `Matrix.mulVec_forwardSubst`. -/
theorem equation_3_22 [NeZero n] {L : Matrix (Fin n) (Fin n) ℝ} (hL : L.IsLowerTriangular)
    (hLu : IsUnit L) (b : Fin n → ℝ) :
    forwardSubst L b 0 = b 0 / L 0 0 ∧
      (∀ i, forwardSubst L b i = (b i - ∑ j with j < i, L i j * forwardSubst L b j) / L i i) ∧
      L *ᵥ forwardSubst L b = b := by
  have hd := (hL.isUnit_iff).1 hLu
  refine ⟨?_, forwardSubst_apply L b, mulVec_forwardSubst b hL hd⟩
  rw [forwardSubst_apply, Finset.sum_eq_zero fun j hj =>
    absurd (mem_filter.1 hj).2 (not_lt.2 (Fin.zero_le j)), sub_zero]

/-- **Equation (3.23)** of [quarteroni2000numerical], backward substitution. Let $n \ge 1$, let
$U \in \mathbb{R}^{n \times n}$ be nonsingular and upper triangular, and let
$b \in \mathbb{R}^n$. The vector $x$ computed by backward substitution satisfies
$$x_n = \frac{b_n}{u_{nn}}, \qquad x_i = \frac{1}{u_{ii}} \Bigl( b_i - \sum_{j > i} u_{ij} x_j
  \Bigr), \quad i = n - 1, \dots, 1,$$
and it solves $Ux = b$.

The vector $x$ is `Matrix.backSubst U b`, and its last index is `⊤`, which is `Fin.last`. The
recurrence is stated for every $i$, including the last index, where the sum is empty. The proof
is the backbone's `Matrix.backSubst_apply` and `Matrix.mulVec_backSubst`. -/
theorem equation_3_23 [NeZero n] {U : Matrix (Fin n) (Fin n) ℝ} (hU : U.IsUpperTriangular)
    (hUu : IsUnit U) (b : Fin n → ℝ) :
    backSubst U b ⊤ = b ⊤ / U ⊤ ⊤ ∧
      (∀ i, backSubst U b i = (b i - ∑ j with i < j, U i j * backSubst U b j) / U i i) ∧
      U *ᵥ backSubst U b = b := by
  have hd := (hU.isUnit_iff).1 hUu
  refine ⟨?_, backSubst_apply U b, mulVec_backSubst b hU hd⟩
  rw [backSubst_apply, Finset.sum_eq_zero fun j hj =>
    absurd (mem_filter.1 hj).2 (not_lt.2 le_top), sub_zero]

/-! ### §3.2.2: rounding error analysis -/

section Rounding

open FloatingPoint

variable {m : RoundingModel ℝ}

/-- For $n \ge 1$, $nu < 1$ implies $u < 1$. -/
private theorem u_lt_one_of_mul_lt_one [NeZero n] (hn : (n : ℝ) * m.u < 1) : m.u < 1 := by
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  nlinarith [m.u_nonneg]

/-- **Equation (3.24)** of [quarteroni2000numerical], the backward error of substitution. Consider
floating-point arithmetic with unit roundoff $u$, let $n \ge 1$ with $nu < 1$, let
$T \in \mathbb{R}^{n \times n}$ be nonsingular, and let $b \in \mathbb{R}^n$. Let either $T$ be
lower triangular and $\hat{x}$ a solution of $Tx = b$ computed by forward substitution, or $T$
be upper triangular and $\hat{x}$ a solution computed by backward substitution. Then there is
$\delta T \in \mathbb{R}^{n \times n}$ with
$$(T + \delta T) \hat{x} = b, \qquad |\delta T| \le \frac{nu}{1 - nu} \, |T| \quad
  \text{entrywise}.$$

The computed solutions are `FloatingPoint.RoundsForwardSubst` and
`FloatingPoint.RoundsBackSubst`. The proof is the backbone's
`FloatingPoint.exists_roundsForwardSubst_eq` and `FloatingPoint.exists_roundsBackSubst_eq`,
which follow Theorem 8.5 of [higham2002accuracy]. -/
theorem equation_3_24 [NeZero n] (hn : (n : ℝ) * m.u < 1) {T : Matrix (Fin n) (Fin n) ℝ}
    (hTu : IsUnit T) {b xhat : Fin n → ℝ} :
    (T.IsLowerTriangular → RoundsForwardSubst m T b xhat →
      ∃ δT : Matrix (Fin n) (Fin n) ℝ,
        δT.abs ≤ₑ (n * m.u / (1 - n * m.u)) • T.abs ∧ (T + δT) *ᵥ xhat = b) ∧
    (T.IsUpperTriangular → RoundsBackSubst m T b xhat →
      ∃ δT : Matrix (Fin n) (Fin n) ℝ,
        δT.abs ≤ₑ (n * m.u / (1 - n * m.u)) • T.abs ∧ (T + δT) *ᵥ xhat = b) := by
  have hu := u_lt_one_of_mul_lt_one hn
  have hcard : (Fintype.card (Fin n) : ℝ) * m.u < 1 := by rwa [Fintype.card_fin]
  constructor
  · intro hT h
    obtain ⟨δT, hδT, hx⟩ := exists_roundsForwardSubst_eq hu hcard hT
      ((hT.isUnit_iff).1 hTu) h
    refine ⟨δT, fun i j => ?_, hx⟩
    simpa [gamma_def] using hδT i j
  · intro hT h
    obtain ⟨δT, hδT, hx⟩ := exists_roundsBackSubst_eq hu hcard hT
      ((hT.isUnit_iff).1 hTu) h
    refine ⟨δT, fun i j => ?_, hx⟩
    simpa [gamma_def] using hδT i j

open scoped Matrix.Norms.Operator in
/-- If $\gamma \ge 0$ and $|\delta T| \le \gamma |T|$ entrywise, then
$\|\delta T\|_\infty \le \gamma \|T\|_\infty$. -/
private theorem linfty_opNorm_le_of_abs_le {δT T : Matrix (Fin n) (Fin n) ℝ} {γ : ℝ}
    (hγ : 0 ≤ γ) (h : δT.abs ≤ₑ γ • T.abs) : ‖δT‖ ≤ γ * ‖T‖ := by
  have h' : δT.abs ≤ₑ (γ • T).abs := fun i j => by
    have := h i j
    simpa [abs_mul, abs_of_nonneg hγ] using this
  calc ‖δT‖ ≤ ‖γ • T‖ := linfty_opNorm_le_of_abs_entrywiseLE h'
    _ = γ * ‖T‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ]

/-- If $T$ is nonsingular, $Tx = b$ with $b \neq 0$, $(T + \delta T) \hat{x} = b$,
$\|\delta T\|_\infty \le \gamma \|T\|_\infty$ and $\gamma K_\infty(T) < 1$, then $\|x -
\hat{x}\|_\infty / \|x\|_\infty \le \gamma K_\infty(T) / (1 - \gamma K_\infty(T))$. -/
private theorem relative_error_le_of_linfty_le {T δT : Matrix (Fin n) (Fin n) ℝ}
    (hTu : IsUnit T) {b x xhat : Fin n → ℝ} (hx : T *ᵥ x = b) (hb : b ≠ 0)
    (hxhat : (T + δT) *ᵥ xhat = b) {γ : ℝ}
    (hδT : lpOpNorm ⊤ δT ≤ γ * lpOpNorm ⊤ T) (hK : γ * condNumber ⊤ T < 1) :
    ‖x - xhat‖ / ‖x‖ ≤ γ * condNumber ⊤ T / (1 - γ * condNumber ⊤ T) := by
  have hne : NeZero n := ⟨fun h => hb (by subst h; exact Subsingleton.elim _ _)⟩
  have hTpos : 0 < lpOpNorm ⊤ T := by
    have h1 := one_le_condNumberLp ⊤ hTu
    rw [condNumberLp] at h1
    refine (lpOpNorm_nonneg ⊤ T).lt_of_ne fun h => ?_
    rw [← h, zero_mul] at h1
    norm_num at h1
  have hK0 : 0 ≤ condNumber ⊤ T := mul_nonneg (lpOpNorm_nonneg _ _) (lpOpNorm_nonneg _ _)
  set r := lpOpNorm ⊤ δT / lpOpNorm ⊤ T with hr
  have hr0 : 0 ≤ r := div_nonneg (lpOpNorm_nonneg _ _) (lpOpNorm_nonneg _ _)
  have hrγ : r ≤ γ := by rw [hr, div_le_iff₀ hTpos]; exact hδT
  have hKr : condNumber ⊤ T * r ≤ γ * condNumber ⊤ T := by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_right hrγ hK0
  have hsmall : lpOpNorm ⊤ δT * lpOpNorm ⊤ T⁻¹ < 1 := by
    calc lpOpNorm ⊤ δT * lpOpNorm ⊤ T⁻¹ = condNumber ⊤ T * r := by
          rw [hr, condNumber]; field_simp
      _ ≤ γ * condNumber ⊤ T := hKr
      _ < 1 := hK
  have h := theorem_3_1 (p := ⊤) hTu hsmall hx hb (δx := xhat - x) (δb := 0)
    (by rw [add_sub_cancel, hxhat, add_zero])
  rw [PiLp.norm_toLp, PiLp.norm_toLp, PiLp.norm_toLp, PiLp.norm_toLp, norm_zero, zero_div,
    zero_add, norm_sub_rev] at h
  refine h.trans ?_
  rw [← hr, div_mul_eq_mul_div]
  have h1 : 0 < 1 - γ * condNumber ⊤ T := by linarith
  have h2 : 0 < 1 - condNumber ⊤ T * r := by linarith
  rw [div_le_div_iff₀ h2 h1]
  nlinarith

/-- **Equation (3.25)** of [quarteroni2000numerical]. Consider floating-point arithmetic with unit
roundoff $u$, let $n \ge 1$ with $nu < 1$, and let $\gamma_n = nu / (1 - nu)$. Let
$T \in \mathbb{R}^{n \times n}$ be nonsingular with $\gamma_n K_\infty(T) < 1$, and let $Tx = b$
with $b \neq 0$. If $T$ is lower triangular and $\hat{x}$ is computed by forward substitution,
or $T$ is upper triangular and $\hat{x}$ is computed by backward substitution, then
$$\frac{\|x - \hat{x}\|_\infty}{\|x\|_\infty} \le \frac{\gamma_n K_\infty(T)}{1 - \gamma_n
  K_\infty(T)}.$$
The right side is $nu K_\infty(T) + O(u^2)$.

**Correction.** The book prints $nu$ in place of $\gamma_n$, its first-order value. The constant
that (3.24) and Theorem 3.1 give is $\gamma_n$. The book also names the $1$-norm and the
Frobenius norm; the statement is for the $\infty$-norm.

By (3.24), $\|\delta T\|_\infty \le \gamma_n \|T\|_\infty$ (the backbone's
`Matrix.linfty_opNorm_le_of_abs_entrywiseLE`), and Theorem 3.1 with $\delta b = 0$ gives the
bound. The condition number $K_\infty(T)$ is `QuarteroniSaccoSaleri.Chapter03.condNumber ⊤ T`. -/
theorem equation_3_25 [NeZero n] (hn : (n : ℝ) * m.u < 1) {T : Matrix (Fin n) (Fin n) ℝ}
    (hTu : IsUnit T) {b x xhat : Fin n → ℝ} (hx : T *ᵥ x = b) (hb : b ≠ 0)
    (hK : n * m.u / (1 - n * m.u) * condNumber ⊤ T < 1) :
    (T.IsLowerTriangular → RoundsForwardSubst m T b xhat →
      ‖x - xhat‖ / ‖x‖ ≤ n * m.u / (1 - n * m.u) * condNumber ⊤ T /
        (1 - n * m.u / (1 - n * m.u) * condNumber ⊤ T)) ∧
    (T.IsUpperTriangular → RoundsBackSubst m T b xhat →
      ‖x - xhat‖ / ‖x‖ ≤ n * m.u / (1 - n * m.u) * condNumber ⊤ T /
        (1 - n * m.u / (1 - n * m.u) * condNumber ⊤ T)) := by
  have hγ : 0 ≤ (n : ℝ) * m.u / (1 - n * m.u) :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg n) m.u_nonneg) (by linarith)
  constructor
  · intro hT h
    obtain ⟨δT, hδT, hxhat⟩ := (equation_3_24 hn hTu).1 hT h
    refine relative_error_le_of_linfty_le hTu hx hb hxhat ?_ hK
    rw [lpOpNorm_top, lpOpNorm_top]
    exact linfty_opNorm_le_of_abs_le hγ hδT
  · intro hT h
    obtain ⟨δT, hδT, hxhat⟩ := (equation_3_24 hn hTu).2 hT h
    refine relative_error_le_of_linfty_le hTu hx hb hxhat ?_ hK
    rw [lpOpNorm_top, lpOpNorm_top]
    exact linfty_opNorm_le_of_abs_le hγ hδT

/-- For an index $i$ of `Fin n`, the number of indices $j$ with $i \le j$ is $n - i$. -/
private theorem card_filter_le_fin (i : Fin n) : #{j : Fin n | i ≤ j} = n - i := by
  rw [← Fin.card_Ici]
  congr 1
  ext j
  simp [Finset.mem_Ici]

/-- **Section 3.2.2** of [quarteroni2000numerical], the improved componentwise bound. Consider
floating-point arithmetic with unit roundoff $u$, and let $n \ge 1$ with $nu < 1$. Let
$U \in \mathbb{R}^{n \times n}$ be nonsingular and upper triangular with $|u_{ij}| \le |u_{ii}|$
for all $j > i$. Let $Ux = b$, and let $\hat{x}$ be computed by backward substitution. Then for
$1 \le i \le n$,
$$|x_i - \hat{x}_i| \le 2^{n-i+1} \, \frac{nu}{1 - nu} \, \max_{j \ge i} |\hat{x}_j|.$$

Indices start at $0$, so the exponent $n - i + 1$ is written `n - i`. The proof is the
backbone's `FloatingPoint.abs_sub_le_of_roundsBackSubst_of_abs_le_diag`, which follows Theorem
8.7 of [higham2002accuracy]. The same bound holds for a lower triangular $L$ with
$|l_{ij}| \le |l_{ii}|$ for $j < i$, by transposition. -/
theorem backSubst_componentwise_error [NeZero n] (hn : (n : ℝ) * m.u < 1)
    {U : Matrix (Fin n) (Fin n) ℝ} (hU : U.IsUpperTriangular) (hUu : IsUnit U)
    (hrow : ∀ i j, i < j → |U i j| ≤ |U i i|) {x b xhat : Fin n → ℝ} (hx : U *ᵥ x = b)
    (h : RoundsBackSubst m U b xhat) (i : Fin n) :
    |x i - xhat i| ≤
      2 ^ (n - i : ℕ) * (n * m.u / (1 - n * m.u)) * ⨆ j : {j : Fin n // i ≤ j}, |xhat j| := by
  have hu := u_lt_one_of_mul_lt_one hn
  have hcard : (Fintype.card (Fin n) : ℝ) * m.u < 1 := by rwa [Fintype.card_fin]
  have hd := (hU.isUnit_iff).1 hUu
  have h := abs_sub_le_of_roundsBackSubst_of_abs_le_diag hu hcard hU hd hrow hx h (i := i)
    (c := ⨆ j : {j : Fin n // i ≤ j}, |xhat j|) fun j hj =>
      le_ciSup (f := fun j : {j : Fin n // i ≤ j} => |xhat j|) (Set.finite_range _).bddAbove
        ⟨j, hj⟩
  rwa [card_filter_le_fin, Fintype.card_fin, gamma_def] at h

/-- **Section 3.2.2** of [quarteroni2000numerical], the diagonally dominant case. Consider
floating-point arithmetic with unit roundoff $u$, and let $n \ge 1$ with $nu < 1$. Let
$U \in \mathbb{R}^{n \times n}$ be nonsingular, upper triangular and diagonally dominant by rows
(Definition 1.24), $\sum_{j \neq i} |u_{ij}| \le |u_{ii}|$. Let $Ux = b$, and let $\hat{x}$ be
computed by backward substitution. Then for every $i$,
$$|x_i - \hat{x}_i| \le (2n - 1) \, \frac{nu}{1 - nu} \, \|\hat{x}\|_\infty.$$

**Reading.** The book says "the same result holds … if $L$ and $U$ are diagonally dominant",
which suggests the bound with $2^{n-i+1}$ of
`QuarteroniSaccoSaleri.Chapter03.backSubst_componentwise_error`. The statement is the bound that
holds under (weak, row) diagonal dominance, which is linear in $n$ and so better.

Diagonal dominance is `Matrix.IsDiagDominant`. The proof is the backbone's
`FloatingPoint.abs_sub_le_of_roundsBackSubst_of_isDiagDominant`, which follows Lemma 8.8 of
[higham2002accuracy]. -/
theorem backSubst_error_of_diagDominant [NeZero n] (hn : (n : ℝ) * m.u < 1)
    {U : Matrix (Fin n) (Fin n) ℝ} (hU : U.IsUpperTriangular) (hUu : IsUnit U)
    (hdom : U.IsDiagDominant) {x b xhat : Fin n → ℝ} (hx : U *ᵥ x = b)
    (h : RoundsBackSubst m U b xhat) (i : Fin n) :
    |x i - xhat i| ≤ (2 * n - 1) * (n * m.u / (1 - n * m.u)) * ‖xhat‖ := by
  have hu := u_lt_one_of_mul_lt_one hn
  have hcard : (Fintype.card (Fin n) : ℝ) * m.u < 1 := by rwa [Fintype.card_fin]
  have hd := (hU.isUnit_iff).1 hUu
  have h := abs_sub_le_of_roundsBackSubst_of_isDiagDominant hu hcard hU hd
    (isDiagDominant_iff_isAbsDiagDominant.1 hdom) hx h
    (c := ‖xhat‖) (fun j => by simpa [Real.norm_eq_abs] using norm_le_pi_norm xhat j) i
  rwa [Fintype.card_fin, gamma_def] at h

end Rounding

/-! ### §3.2.3: the inverse of a triangular matrix -/

section Inverse

variable {U : Matrix (Fin n) (Fin n) ℝ}

/-- **Equation (3.26)** of [quarteroni2000numerical]. Let $U \in \mathbb{R}^{n \times n}$ be
nonsingular and upper triangular, and let $v_i$ be the $i$-th column of $V = U^{-1}$. Then
$U v_i = e_i$, so $v_i$ is computed by backward substitution (3.23) from the canonical basis
vector $e_i$.

The column $v_i$ is `U⁻¹.col i`, and $e_i$ is `Pi.single i 1`. The proof is the backbone's
`Matrix.inv_col_eq_backSubst`. -/
theorem equation_3_26 (hU : U.IsUpperTriangular) (hUu : IsUnit U) (i : Fin n) :
    U *ᵥ U⁻¹.col i = Pi.single i 1 ∧ U⁻¹.col i = backSubst U (Pi.single i 1) := by
  have hd := (hU.isUnit_iff).1 hUu
  have h : U⁻¹.col i = backSubst U (Pi.single i 1) := inv_col_eq_backSubst hU hd i
  exact ⟨by rw [h, mulVec_backSubst _ hU hd], h⟩

/-- A leading principal submatrix of an upper triangular matrix is upper triangular. -/
private theorem isUpperTriangular_leadingPrincipalSubmatrix (hU : U.IsUpperTriangular)
    (k : Fin n) : (U.leadingPrincipalSubmatrix k).IsUpperTriangular :=
  fun _ _ hij => hU hij

/-- **Equation (3.27)** of [quarteroni2000numerical]. Let $U \in \mathbb{R}^{n \times n}$ be
nonsingular and upper triangular. For $k = 1, \dots, n$, let $U^{(k)}$ be the leading principal
submatrix of order $k$ of $U$, let $l_k \in \mathbb{R}^k$ be the vector whose only nonzero entry
is a $1$ in the $k$-th (last) position, and let $v'_k$ be the solution of $U^{(k)} v'_k = l_k$
computed by backward substitution (3.23). Then $v'_k$ solves this system, and it consists of the
first $k$ entries of the $k$-th column of $U^{-1}$.

**Typo.** The book describes $l_k$ as the vector of $\mathbb{R}^k$ whose first entry is $1$.
Since $v'_k$ is the leading part of the $k$-th column of $U^{-1}$, it solves
$U^{(k)} v'_k = e_k$ with the $1$ in the last position, as the recurrence (3.28),
$v'_{kk} = u_{kk}^{-1}$, confirms.

Indices start at $0$: for `k : Fin n`, the matrix `U.leadingPrincipalSubmatrix k` has order
$k + 1$ and is indexed by the indices $j \le k$, and $l_k$ is `Pi.single ⟨k, le_rfl⟩ 1`. The
proof uses that $(U^{(k)})^{-1}$ is the leading block of $U^{-1}$ (the backbone's
`Matrix.inv_toBlock_le_of_isUpperTriangular`) and `Matrix.inv_col_eq_backSubst`. -/
theorem equation_3_27 (hU : U.IsUpperTriangular) (hUu : IsUnit U) (k : Fin n) :
    U.leadingPrincipalSubmatrix k *ᵥ
        backSubst (U.leadingPrincipalSubmatrix k) (Pi.single ⟨k, le_rfl⟩ 1) =
      Pi.single ⟨k, le_rfl⟩ 1 ∧
    ∀ j : {j : Fin n // j ≤ k},
      backSubst (U.leadingPrincipalSubmatrix k) (Pi.single ⟨k, le_rfl⟩ 1) j = U⁻¹ j k := by
  have hd := (hU.isUnit_iff).1 hUu
  have hUk := isUpperTriangular_leadingPrincipalSubmatrix hU k
  have hdk : ∀ i : {j : Fin n // j ≤ k}, U.leadingPrincipalSubmatrix k i i ≠ 0 := fun i => hd i
  refine ⟨mulVec_backSubst _ hUk hdk, fun j => ?_⟩
  -- the backbone statements carry the `DecidableEq {j // j ≤ k}` instance of the linear order,
  -- this goal the one of the subtype; `convert` identifies the two
  have h1 : (U.leadingPrincipalSubmatrix k)⁻¹ j ⟨k, le_rfl⟩
      = backSubst (U.leadingPrincipalSubmatrix k) (Pi.single ⟨k, le_rfl⟩ 1) j := by
    convert congrFun (inv_col_eq_backSubst hUk hdk ⟨k, le_rfl⟩) j
  have h2 := congrFun (congrFun (inv_toBlock_le_of_isUpperTriangular hU hd k) j) ⟨k, le_rfl⟩
  exact h1.symm.trans h2

/-- **Equation (3.28)** of [quarteroni2000numerical], the inversion algorithm for upper triangular
matrices. Let $U \in \mathbb{R}^{n \times n}$ be nonsingular and upper triangular, and write
$U^{-1} = (v'_{ik})$. For $k = n, n - 1, \dots, 1$, the entries of the $k$-th column of $U^{-1}$
satisfy
$$v'_{kk} = u_{kk}^{-1}, \qquad v'_{ik} = -u_{ii}^{-1} \sum_{j=i+1}^{k} u_{ij} v'_{jk}, \quad
  i = k - 1, \dots, 1,$$
and $v'_{ik} = 0$ for $i > k$.

The proof is the backbone's `Matrix.inv_apply_self_of_isUpperTriangular`,
`Matrix.inv_apply_of_isUpperTriangular` and `Matrix.inv_apply_of_isUpperTriangular_of_lt`. -/
theorem equation_3_28 (hU : U.IsUpperTriangular) (hUu : IsUnit U) (k : Fin n) :
    U⁻¹ k k = (U k k)⁻¹ ∧
      (∀ i, i < k → U⁻¹ i k = -(U i i)⁻¹ * ∑ j with i < j ∧ j ≤ k, U i j * U⁻¹ j k) ∧
      ∀ i, k < i → U⁻¹ i k = 0 := by
  have hd := (hU.isUnit_iff).1 hUu
  exact ⟨inv_apply_self_of_isUpperTriangular hU hd k,
    fun i hik => inv_apply_of_isUpperTriangular hU hd hik,
    fun i hki => inv_apply_of_isUpperTriangular_of_lt hU hki⟩

end Inverse

end QuarteroniSaccoSaleri.Chapter03
