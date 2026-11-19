/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.Arnoldi
import Numlib.Krylov.Hessenberg
import Numlib.Krylov.Iterate
import Numlib.Krylov.Lanczos
import Numlib.Krylov.Relations
import Numlib.Krylov.Subspace
import Numlib.Projection.Basic
import NumlibSurface.FongSaunders.Section03

/-!
# Fong and Saunders, Section 4: The exact relations behind the numerical comparison

This module formalizes the mathematical content of Section 4 of [fong2012cg], which is mostly an
experimental study. It proves the relation (4.1) between the residual norms of CG and MINRES,
$$\|r_k^C\| = \frac{\|r_k^M\|}{\sqrt{1 - \|r_k^M\|^2 / \|r_{k-1}^M\|^2}},$$
the telescoping product of residual ratios of Section 4.1.1, and the description in Section 4.2 of
the MINRES iterate as $x_k^M = V_k y_k^M$, where $y_k^M$ solves the least-squares subproblem
$\min_y \|\underline{T}_k y - \beta_1 e_1\|$ with $\beta_1 = \|b\|$. For a symmetric, possibly
indefinite system, it also proves the theorem of [steihaug1983conjugate] that Section 4.2 quotes:
the CG solution norms increase strictly as long as $p_j^T A p_j > 0$. It proves the analogue for CR,
whose iterates are then the MINRES iterates.

The proofs specialize `Numlib.Krylov.Relations`, `Numlib.Krylov.Hessenberg` and the strict
monotonicity theorems `CG.norm_iterate_lt_of_re_inner_apply_direction_pos` and
`CR.norm_iterate_lt_of_pos` of the backbone. The indefinite example (4.2) of Section 4.2 is
formalized in `NumlibSurface.FongSaunders.Section05`, together with Table 5.1.

## Main results

* Equation (4.1), `FongSaunders.equation_4_1` and `FongSaunders.equation_4_1_minres`: for $k \ge 1$
  and $r_k^M \neq 0$, $\|r_k^C\| = \|r_k^M\| / \sqrt{1 - \|r_k^M\|^2 / \|r_{k-1}^M\|^2}$.
* Section 4.1.1, `FongSaunders.prod_ratio_residual`: $\prod_{k=1}^{l} \|r_k\| / \|r_{k-1}\| =
  \|r_l\| / \|b\|$ when $r_0 = b$ and the residuals before step $l$ are nonzero.
* Section 4.2, `FongSaunders.minres_subproblem`: for $k \le \ell$, $V_k y$ is the MINRES iterate if
  and only if $y$ minimizes $\|\beta_1 e_1 - \underline{T}_k y\|$.
* Section 4.2, `FongSaunders.minres_coeff_unique`: for $k \le \ell$, the coordinate vector $y_k^M$
  of the MINRES iterate is unique.
* Section 4.2, `FongSaunders.steihaug_cg`: for symmetric $A$, the CG solution norms increase
  strictly as long as $p_j^T A p_j > 0$.
* Section 4.2, `FongSaunders.steihaug_cr`: for symmetric $A$, the CR solution norms increase
  strictly if $\rho_j = r_j^T A r_j > 0$ at every iteration before termination.

## Conventions

* The CG residual is $r_k^C$, the residual of `FongSaunders.cg`. The MINRES residual $r_k^M$ is the
  CR residual $r_k$ of `FongSaunders.cr`, or $b - A x_k$ for a sequence $(x_k)$ of MINRES iterates.

## Deviations from the source

* **Section 4.1.1, product of residual ratios** (generalization). The exact identity
  holds for arbitrary sequences with nonzero denominators. The approximation by the
  stopping tolerance is outside the identity. See `FongSaunders.prod_ratio_residual`.
* **Equation (4.1)** (reading). The result assumes $r_k^M \neq 0$, excluding the step
  that first reaches the exact solution. See `FongSaunders.equation_4_1` and
  `FongSaunders.equation_4_1_minres`.
* **Section 4.2, MINRES coordinates** (reading). The source considers symmetric systems that
  are nonsingular or consistent. The coordinate results here require positive definiteness.
  See `FongSaunders.minres_subproblem` and `FongSaunders.minres_coeff_unique`.
* **Steihaug's theorem for CG** (reading). The curvature test uses the direction
  $p_{j-1}$ entering iteration $j$, as in Table 2.1. See `FongSaunders.steihaug_cg`.
* **Steihaug's theorem for CR and MINRES** (reading). The paper assumes $p_j^T A p_j > 0$ and
  $r_j^T A r_j > 0$ for $1 \le j \le k$. Here the sufficient condition uses
  $r_j^T A r_j > 0$ at every iteration before termination. See `FongSaunders.steihaug_cr`.

## Not formalized

* **The test set and the diagonal preconditioning of Section 4.** They are empirical.
* **Figures 4.1–4.8 and their percentages of monotone steps.** They are empirical.
* **The "cumulative minimum" heuristic of Section 4.1.1.** It is empirical.
* **The relation to MINRES-QLP in Section 4.2.** It rests on the work of Choi, Paige and Saunders,
  the paper draws no theorem from it, and its missing ingredient, the QLP factorization
  $R_k P_k = L_k$, belongs in the backbone module `Numlib.Krylov.Singular`.
-/

namespace FongSaunders

open Krylov Matrix

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {b : Vec n}

/-- For Algorithm CR, $b - A x_k = r_k$, in the form that the backbone residual lemmas produce. -/
private theorem cr_res (k : ℕ) : b - Matrix.toEuclideanLin A (cr A b k).x = (cr A b k).r :=
  (cr_residual_eq k).symm

/-- For Algorithm CG, $b - A x_k^C = r_k^C$, in the form that the backbone residual lemmas produce.
-/
private theorem cg_res (k : ℕ) : b - Matrix.toEuclideanLin A (cg A b k).x = (cg A b k).r :=
  (cg_residual_eq k).symm

/-! ### Equation (4.1) -/

/-- **Equation (4.1)** of [fong2012cg]. Let $A \in \mathbb{R}^{n \times n}$ be positive definite,
and let $k \ge 1$. If the MINRES residual satisfies $r_k^M \neq 0$, then the CG residual
satisfies $$\|r_k^C\| = \frac{\|r_k^M\|}{\sqrt{1 - \|r_k^M\|^2 / \|r_{k-1}^M\|^2}}.$$

**Reading.** The source gives the formula without a nonzero condition on $r_k^M$. The result
here requires $r_k^M \neq 0$ to apply the inverse-square residual identity. At the first zero
residual, both sides of the source formula are zero if $r_{k-1}^M \neq 0$.

The relation is Lemma 5.4.1 of [greenbaum1997iterative], also due to Titley-Péloquin. The
statement is written for step $k + 1$ with $k \in \mathbb{N}$, so that $k \ge 1$ holds by
construction, and $r_k^M$ is the CR residual $r_k$. The proof rearranges the harmonic identity
$1 / \|r_k^M\|^2 = 1 / \|r_{k-1}^M\|^2 + 1 / \|r_k^C\|^2$, which is
`Krylov.inv_sq_norm_residual_minRes`. -/
theorem equation_4_1 (hA : A.PosDef) (k : ℕ) (hk : (cr A b (k + 1)).r ≠ 0) :
    ‖(cg A b (k + 1)).r‖
      = ‖(cr A b (k + 1)).r‖ /
        Real.sqrt (1 - ‖(cr A b (k + 1)).r‖ ^ 2 / ‖(cr A b k).r‖ ^ 2) := by
  have hG := isMINRESIterate_iff.1 (cr_isMINRESIterate (b := b) hA k)
  have hG' := isMINRESIterate_iff.1 (cr_isMINRESIterate (b := b) hA (k + 1))
  have hF := cg_isGalerkinIterate (b := b) hA (k + 1)
  have h0 : b - Matrix.toEuclideanLin A (cr A b (k + 1)).x ≠ 0 := by rw [cr_res]; exact hk
  have key := Krylov.inv_sq_norm_residual_minRes hG hG' hF h0
  rw [cr_res, cr_res, cg_res] at key
  have hMle : ‖(cr A b (k + 1)).r‖ ≤ ‖(cr A b k).r‖ := by
    have h := Krylov.IsMinResidualIterate.norm_residual_antitone
      (x := fun j => (cr A b j).x)
      (fun j => isMINRESIterate_iff.1 (cr_isMINRESIterate hA j)) (Nat.le_succ k)
    simp only at h
    rwa [cr_res, cr_res] at h
  have hMC : ‖(cr A b (k + 1)).r‖ ≤ ‖(cg A b (k + 1)).r‖ := by
    have h := Krylov.norm_residual_minRes_le_galerkin hG' hF
    rwa [cr_res, cg_res] at h
  have hM : 0 < ‖(cr A b (k + 1)).r‖ := norm_pos_iff.2 hk
  have hM0 : 0 < ‖(cr A b k).r‖ := lt_of_lt_of_le hM hMle
  have hC : 0 < ‖(cg A b (k + 1)).r‖ := lt_of_lt_of_le hM hMC
  have hMne : ‖(cr A b (k + 1)).r‖ ≠ 0 := hM.ne'
  have hM0ne : ‖(cr A b k).r‖ ≠ 0 := hM0.ne'
  have hCne : ‖(cg A b (k + 1)).r‖ ≠ 0 := hC.ne'
  have hval : 1 - ‖(cr A b (k + 1)).r‖ ^ 2 / ‖(cr A b k).r‖ ^ 2
      = (‖(cr A b (k + 1)).r‖ / ‖(cg A b (k + 1)).r‖) ^ 2 := by
    rw [div_pow]
    field_simp at key ⊢
    linarith
  rw [hval, Real.sqrt_sq (by positivity)]
  field_simp

/-- **Equation (4.1)** of [fong2012cg], for MINRES iterates. Let $A \in \mathbb{R}^{n \times n}$ be
positive definite, let $(x_k)$ be a sequence such that each $x_k$ is a MINRES iterate at step
$k$, and let $r_k^M = b - A x_k$. For $k \ge 1$ with $r_k^M \neq 0$, $$\|r_k^C\| =
\frac{\|r_k^M\|}{\sqrt{1 - \|r_k^M\|^2 / \|r_{k-1}^M\|^2}}.$$

**Reading.** As in `FongSaunders.equation_4_1`, the statement assumes $r_k^M \neq 0$,
leaving out the step that first reaches the exact solution.

The statement is written for step $k + 1$ with
$k \in \mathbb{N}$. -/
theorem equation_4_1_minres (hA : A.PosDef) {x : ℕ → Vec n} (hx : ∀ k, IsMINRESIterate A b k (x k))
    (k : ℕ) (hk : b - A ⬝ x (k + 1) ≠ 0) :
    ‖(cg A b (k + 1)).r‖
      = ‖b - A ⬝ x (k + 1)‖ /
        Real.sqrt (1 - ‖b - A ⬝ x (k + 1)‖ ^ 2 / ‖b - A ⬝ x k‖ ^ 2) := by
  have hres : ∀ j, b - A ⬝ x j = (cr A b j).r := fun j => by
    rw [(isMINRESIterate_iff_eq_cr hA j (x j)).1 (hx j), ← cr_residual_eq]
  rw [hres] at hk
  rw [hres, hres]
  exact equation_4_1 hA k hk

/-! ### The telescoping product of residual ratios (Section 4.1.1) -/

/-- **Section 4.1.1** of [fong2012cg], the telescoping product. Let $b \neq 0$, and let $(r_k)$ be a
sequence of vectors with $r_0 = b$. If $l \in \mathbb{N}$ and $r_0, r_1, \dots, r_{l-1}$ are
nonzero, then $$\prod_{k=1}^{l} \frac{\|r_k\|}{\|r_{k-1}\|} = \frac{\|r_l\|}{\|b\|}.$$

**Generalization.** The source considers residuals at a stopping iteration and compares
the final ratio approximately with the tolerance. The exact telescoping identity applies
to any sequence with the stated denominators.

The condition $b \neq 0$ follows
from the other conditions when $l \ge 1$; it is stated so that the case $l = 0$ is also covered.
The product is written over $k < l$ with the factor $\|r_{k+1}\| / \|r_k\|$. -/
theorem prod_ratio_residual (r : ℕ → Vec n) (hb : b ≠ 0) (hr0 : r 0 = b) (l : ℕ)
    (hne : ∀ k < l, r k ≠ 0) :
    ∏ k ∈ Finset.range l, ‖r (k + 1)‖ / ‖r k‖ = ‖r l‖ / ‖b‖ := by
  induction l with
  | zero => simp [hr0, div_self (norm_ne_zero_iff.2 hb)]
  | succ l ih =>
    have hl : ‖r l‖ ≠ 0 := norm_ne_zero_iff.2 (hne l (Nat.lt_succ_self l))
    rw [Finset.prod_range_succ, ih fun k hk => hne k (by omega)]
    field_simp

/-! ### The MINRES subproblem in Lanczos coordinates (Section 4.2) -/

/-- If $A$ is symmetric, then the Hessenberg matrix `Arnoldi.hessenberg` of the Arnoldi process for
`Matrix.toEuclideanLin A` and $b$ is the Lanczos matrix $\underline{T}_k$. -/
theorem hessenberg_eq_lanczosT (hA : A.IsSymm) (k : ℕ) :
    Arnoldi.hessenberg (Matrix.toEuclideanLin A) b k = lanczosT A b k := by
  rw [Lanczos.hessenberg_eq_map_tridiagExt b (isSymmetric_toEuclideanLin hA) k]
  ext i j
  simp

/-- **Section 4.2** of [fong2012cg], the MINRES subproblem. Let $A \in \mathbb{R}^{n \times n}$ be
positive definite, let $\ell$ be the termination step of the Lanczos process, and let
$k \le \ell$. For $y \in \mathbb{R}^k$, the vector $V_k y$ is a MINRES iterate at step $k$ if
and only if $y$ minimizes $$\|\beta_1 e_1 - \underline{T}_k z\| \quad \text{over } z \in
\mathbb{R}^k, \qquad \beta_1 = \|b\|.$$

**Reading.** The source uses this least-squares characterization for symmetric systems,
including indefinite ones. The result here assumes positive definiteness.

The vector $\beta_1 e_1 \in \mathbb{R}^{k+1}$ is `Krylov.firstVec ‖b‖ (k + 1)`, and $V_k y$ is
the sum $\sum_j y_j v_j$ of the Lanczos vectors. -/
theorem minres_subproblem (hA : A.PosDef) (k : ℕ) (hk : k ≤ lanczosTerm A b) (y : Fin k → ℝ) :
    IsMINRESIterate A b k (∑ j, y j • lanczosVec A b j) ↔
      IsMinOn (fun z : Fin k → ℝ =>
        ‖(WithLp.toLp 2 (Krylov.firstVec ‖b‖ (k + 1) - (lanczosT A b k).mulVec z) :
          Vec (k + 1))‖) Set.univ y := by
  have hK := Krylov.isMinResidualIterate_iff_isMinOn (A := Matrix.toEuclideanLin A) (b := b)
    (x₀ := 0) (m := k) (by rwa [sub_mulVecE_zero]) y
  rw [sub_mulVecE_zero, hessenberg_eq_lanczosT (hA.isSymm),
    RCLike.ofReal_real_eq_id, id_eq] at hK
  rw [isMINRESIterate_iff, ← hK, zero_add]

/-- **Section 4.2** of [fong2012cg], uniqueness of the MINRES coordinates. Let
$A \in \mathbb{R}^{n \times n}$ be positive definite, let $\ell$ be the termination step of the
Lanczos process, and let $k \le \ell$. Then there is exactly one $y \in \mathbb{R}^k$ such that
$V_k y$ is a MINRES iterate at step $k$.

**Reading.** The source states uniqueness for a nonsingular or consistent symmetric system.
The result here assumes positive definiteness, which ensures uniqueness of the MINRES iterate.
-/
theorem minres_coeff_unique (hA : A.PosDef) (k : ℕ) (hk : k ≤ lanczosTerm A b) :
    ∃! y : Fin k → ℝ, IsMINRESIterate A b k (∑ j, y j • lanczosVec A b j) := by
  have hinj : Function.Injective fun j : Fin k => (⟨(j : ℕ), lt_of_lt_of_le j.2 hk⟩ :
      Fin (lanczosTerm A b)) := by
    intro i j hij
    simpa [Fin.ext_iff] using hij
  have horth : Orthonormal ℝ fun j : Fin k => lanczosVec A b (j : ℕ) :=
    (lanczosVec_orthonormal A b).comp
      (fun j : Fin k => (⟨(j : ℕ), lt_of_lt_of_le j.2 hk⟩ : Fin (lanczosTerm A b))) hinj
  have hli := horth.linearIndependent
  obtain ⟨x, hx⟩ := Krylov.exists_isMinResidualIterate (Matrix.toEuclideanLin A) b 0 k
  obtain ⟨y, hy⟩ := (mem_krylov_iff_exists_lanczos A b k x).1
    (sub_zero_mem_subspace_iff.1 hx.mem)
  have hxy : IsMINRESIterate A b k (∑ j, y j • lanczosVec A b (j : ℕ)) := by
    rw [← hy]; exact isMINRESIterate_iff.2 hx
  refine ⟨y, hxy, fun z hz => ?_⟩
  have heq : ∑ j, z j • lanczosVec A b (j : ℕ) = ∑ j, y j • lanczosVec A b (j : ℕ) :=
    isMINRESIterate_unique hA hz hxy
  have hzero : ∑ j, (z - y) j • lanczosVec A b (j : ℕ) = 0 := by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, heq, sub_self]
  funext j
  have := Fintype.linearIndependent_iff.1 hli (z - y) hzero j
  simpa [sub_eq_zero] using this

/-! ### Steihaug's theorem on indefinite systems (Section 4.2) -/

/-- **Section 4.2** of [fong2012cg] (Steihaug's theorem [steihaug1983conjugate]). Let
$A \in \mathbb{R}^{n \times n}$ be symmetric, possibly indefinite, and let $x_j^C$ and $p_j^C$
be the iterates and the directions of Algorithm CG for $Ax = b$ from $x_0 = 0$. Let
$k \in \mathbb{N}$, and suppose that $(p_j^C)^T A p_j^C > 0$ for $j = 0, \dots, k - 1$, the
directions of iterations $1, \dots, k$. Then $$\|x_0^C\| < \|x_1^C\| < \dots < \|x_k^C\|.$$

**Reading.** The source writes $p_j^T A p_j>0$ for iterations $1,\ldots,k$. In Table 2.1,
iteration $j$ uses $p_{j-1}$ to update $x_{j-1}$, so the hypothesis tests $p_0,\ldots,p_{k-1}$.

The conclusion is stated as $\|x_i^C\| < \|x_{i+1}^C\|$ for every $i < k$. -/
theorem steihaug_cg (hA : A.IsSymm) {k : ℕ}
    (hpos : ∀ j < k, 0 < ⟪(cg A b j).p, A ⬝ (cg A b j).p⟫_ℝ) {i : ℕ} (hi : i < k) :
    ‖(cg A b i).x‖ < ‖(cg A b (i + 1)).x‖ := by
  simp only [cg_x]
  refine CG.norm_iterate_lt_of_re_inner_apply_direction_pos b (isSymmetric_toEuclideanLin hA)
    (fun j hj => ?_) hi
  rw [RCLike.re_to_real, real_inner_comm]
  simpa only [cg_p] using hpos j hj

/-- **Section 4.2** of [fong2012cg], Steihaug's theorem for CR and MINRES. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric, possibly indefinite, and let $\ell$ be the
termination step of Algorithm CR for $Ax = b$. Suppose that $\rho_j = r_j^T A r_j > 0$ for every
$j < \ell$. Then for every $i < \ell$, the CR iterates satisfy $$\|x_i\| < \|x_{i+1}\|.$$

**Reading.** The paper states the property for CR and MINRES as long as both $p_j^T A p_j > 0$
and $r_j^T A r_j > 0$ for all iterations $1 \le j \le k$, which is a local hypothesis. Its proof
of Theorem 2.2(d) expands $r_i$ over all the remaining steps, so a single negative $\rho_m$
after step $k$ breaks the argument. The statement here therefore reads the hypothesis globally
and assumes $\rho_j > 0$ up to the termination step $\ell$. The identity
$r_j^T A p_j = \rho_j$ gives $A p_j \neq 0$ for the step length. The strict-increase proof
`CR.norm_iterate_lt_of_pos` uses these hypotheses without a separate curvature condition.

The termination step $\ell$ is `FongSaunders.crTerm A b`. If no CR residual vanishes, its value
is $0$ and the statement says nothing. Under the hypotheses,
`CR.isMinResidualIterate_of_no_breakdown` identifies $x_k$ with the MINRES iterate, so the
property transfers to MINRES. -/
theorem steihaug_cr (hA : A.IsSymm) (hpos : ∀ j < crTerm A b, 0 < (cr A b j).ρ) {i : ℕ}
    (hi : i < crTerm A b) : ‖(cr A b i).x‖ < ‖(cr A b (i + 1)).x‖ := by
  have hne : {k | (cr A b k).r = 0}.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [crTerm, h, Nat.sInf_empty] at hi
    exact Nat.not_lt_zero i hi
  have hstop : (CR.iterate (toEuclideanLin A) b 0 (crTerm A b)).r = 0 := by
    rw [← cr_r]; exact Nat.sInf_mem hne
  simp only [cr_x]
  refine CR.norm_iterate_lt_of_pos b (isSymmetric_toEuclideanLin hA) hstop (fun j hj => ?_) hi
  rw [RCLike.re_to_real]
  simpa only [cr_rho, cr_r] using hpos j hj

end FongSaunders
