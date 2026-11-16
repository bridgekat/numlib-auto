/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.CartisGouldToint.Chapter09.Section03
import NumlibSurface.CartisGouldToint.Chapter10.Section01

/-!
# Cartis, Gould and Toint, Section 10.2: Computational details for regularization methods

This module formalizes §10.2 of [cartis2022evaluation]: the computation of the Krylov subspace
solutions of the regularization subproblem (8.1.3). Let $H \in \mathbb{R}^{n \times n}$ be
symmetric, $M \in \mathbb{R}^{n \times n}$ positive definite, $\sigma > 0$ and $r > 2$. On the
Krylov subspace $\mathcal{K}_k = \mathcal{K}(M^{-1}H, M^{-1}g, k)$ with the Lanczos basis $Q_k$ and
the Lanczos tridiagonal matrix $T_k$ of §10.1, the subspace solution is $s_k = Q_k \bar{s}_k$, where
$\bar{s}_k$ globally minimizes the reduced problem (10.1.6)
$$\min_{\bar{s} \in \mathbb{R}^k} \; \gamma_1 \langle e_1, \bar{s} \rangle + \tfrac12 \langle
  \bar{s}, T_k \bar{s} \rangle + \tfrac{\sigma}{r} \|\bar{s}\|^r, \qquad \gamma_1 =
  \|g\|_{M^{-1}}.$$

The module proves that $\bar{s}_k$ solves $(T_k + \lambda_k I_k) \bar{s}_k = -\gamma_1 e_1$ with
$T_k + \lambda_k I_k$ positive definite, where $\lambda_k = \sigma \|s_k\|_M^{r-2}$. It formalizes
the factorization and the solve of the shifted tridiagonal system (Algorithms 10.2.1–10.2.2), the
monotonicity of the multipliers and norms in $k$ (Lemma 10.2.1), the one-dimensional start (10.2.7),
the bound on the model gradient at $s_k$ in terms of the condition number $\kappa_k$ of
$T_k + \lambda_k I_k$ (Theorem 10.2.2), and a bound on the number of Lanczos iterations before the
stopping rule (9.3.14b) holds (Corollary 10.2.3). The proofs use the backbone modules
`Numlib.Optimization.Subproblem.Krylov`, `Numlib.Optimization.Subproblem.KrylovConvergence` and
`Numlib.LinearAlgebra.Matrix.TridiagonalLDL`.

## Main definitions

* Algorithm 10.2.1, `CartisGouldToint.Chapter10.algorithm_10_2_1`: the factorization
  $T_k + \lambda I_k = L_k D_k L_k^T$ of a shifted symmetric tridiagonal matrix, or the exit "not
  positive definite".
* Algorithm 10.2.2, `CartisGouldToint.Chapter10.algorithm_10_2_2`: the solve of
  $(T_k + \lambda I_k) x = b$ with the factors of Algorithm 10.2.1.
* (10.2.8), `CartisGouldToint.Chapter10.conditionNumber_10_2_8`: the condition number $\kappa_k =
  (\theta_{k,k} + \lambda)/(\theta_{1,k} + \lambda)$ from the extreme Ritz values.
* (10.2.10), `CartisGouldToint.Chapter10.kappaStar`: the largest condition number $\kappa_* =
  \max_{1 \le k \le \text{grade}} \kappa_k$.

## Main results

* (10.2.2)–(10.2.3), `CartisGouldToint.Chapter10.subspace_optimality_10_2_2`: $(T_k + \lambda_k I_k)
  \bar{s}_k = -\gamma_1 e_1$, and $T_k + \lambda_k I_k$ is positive definite, so $\bar{s}_k$ is
  unique.
* Algorithm 10.2.1, `CartisGouldToint.Chapter10.algorithm_10_2_1_spec`: the algorithm exits exactly
  when $T_k + \lambda I_k$ is not positive definite, and otherwise returns an $LDL^T$ factorization
  with a positive diagonal.
* Algorithm 10.2.2, `CartisGouldToint.Chapter10.algorithm_10_2_2_spec`: the algorithm solves
  $(T_k + \lambda I_k) x = b$ (10.2.4).
* Lemma 10.2.1, `CartisGouldToint.Chapter10.lemma_10_2_1`: the multipliers $\lambda_k$ and the norms
  $\|s_k\|_M$ increase with $k$ and are bounded by those of the global minimizer.
* (10.2.7), `CartisGouldToint.Chapter10.start_10_2_3`: for $k = 1$ the multiplier is the unique
  admissible root of a scalar secular equation.
* Theorem 10.2.2, `CartisGouldToint.Chapter10.theorem_10_2_2`: the model gradient at $s_k$ decays
  like $((\sqrt{\kappa_k} - 1)/(\sqrt{\kappa_k} + 1))^{k-1}$ (10.2.9).
* Corollary 10.2.3, `CartisGouldToint.Chapter10.corollary_10_2_3`: the stopping rule (9.3.14b) holds
  after a number of iterations of order $\log A / \log((\sqrt{\kappa_*} + 1)/(\sqrt{\kappa_*} -
  1))$.

## Conventions

* The matrices $Q_k$, $T_k$ and the vector $Q_k^T g$ are `CartisGouldToint.Chapter10.lanczosBasis`,
  `CartisGouldToint.Chapter10.lanczosTridiag` and `CartisGouldToint.Chapter10.lanczosGrad`. The
  grade of $M^{-1}H$ with respect to $M^{-1}g$ is `CartisGouldToint.Chapter10.gradeHM`.
* A global minimizer of the reduced problem (10.1.6) is
  `CartisGouldToint.Chapter08.IsRegularizationSolution` for the data $Q_k^T g$, $T_k$ and the
  scaling matrix $I_k$. Below the grade, $Q_k^T g = \gamma_1 e_1$.
* $\|v\|_M = \sqrt{\langle v, M v \rangle}$ is `CartisGouldToint.Chapter08.mNorm M v`.

## Implementation notes

* The norm $\|M^{-1}H\|$ in Theorem 10.2.2 and Corollary 10.2.3 is the operator norm of $M^{-1}H$
  induced by the scaled norm $\|\cdot\|_M$, that is, the norm of `Subproblem.scaledOp H hM` on the
  $M$-inner product space `Subproblem.ScaledSpace`. It equals $\|M^{-1/2} H M^{-1/2}\|_2$, and with
  this reading the identity (B.10.4) holds. It is bounded by the Euclidean operator norm of
  $M^{-1}H$ (`Subproblem.norm_scaledOp_le`).
* The algorithms of §10.2.2 use $0$-based indices: `ρ i` and `γ i` are the book's $\rho_{i+1}$ and
  $\gamma_{i+1}$.

## Deviations from the source

* **Lemma 10.2.1** (typo). The source refers to "a global minimizer of (8.1.4)"; (8.1.4) is the
  model, and the problem is (8.1.3). See `CartisGouldToint.Chapter10.lemma_10_2_1`.
* **Corollary 10.2.3** (correction). The printed bound $\lceil \log A / \log((\sqrt{\kappa_*} +
  1)/(\sqrt{\kappa_*} - 1)) \rceil + 1$ cannot hold when $\log A < 0$ and is undefined for
  $\kappa_* = 1$. The ceiling is $\lceil \cdot \rceil_+$, the case $\kappa_* = 1$ gives some
  $k \le \min(2, \text{grade})$, and the hypothesis $g \neq 0$ is added. See
  `CartisGouldToint.Chapter10.corollary_10_2_3`.
-/

open Matrix Set
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter10

open Subproblem CartisGouldToint.Chapter08 CartisGouldToint.Chapter09

variable {n : ℕ} {H M : Matrix (Fin n) (Fin n) ℝ} {g : EuclideanSpace ℝ (Fin n)}

/-! ### The scaled form of the Krylov subproblems -/

section Scaled

/-- Let $M$ be positive definite. If $1 \le k \le \operatorname{grade}(M^{-1}H, M^{-1}g)$, then the
scaled gradient $M^{-1}g$ is nonzero; in particular $g \neq 0$. -/
theorem ne_zero_of_le_gradeHM (hM : M.PosDef) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ gradeHM H M g) :
    scaledGrad hM g ≠ 0 := fun hb => by
  rw [gradeHM_eq hM, hb, Krylov.grade_zero] at hk
  omega

/-- For a positive definite $M$, the Lanczos tridiagonal matrix $T_k$ is symmetric. -/
theorem lanczosTridiag_isHermitian (hM : M.PosDef) (k : ℕ) :
    (lanczosTridiag hM H g k).IsHermitian :=
  Matrix.isHermitian_iff_isSymm.2 (Lanczos.tridiag_isSymm _ _ _)

/-- For a positive definite $M$ and every $y \in \mathbb{R}^k$, the vector $Q_k y$ lies in the
Krylov subspace $\mathcal{K}_k = \mathcal{K}(M^{-1}H, M^{-1}g, k)$ of the $M$-inner product
space. -/
theorem toScaled_lanczosBasis_mem (hM : M.PosDef) {k : ℕ} (y : EuclideanSpace ℝ (Fin k)) :
    toScaled hM (toEuclideanLin (lanczosBasis hM H g k) y) ∈
      Krylov.subspace (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g) k :=
  (toScaled_mem_krylov_iff hM).2 (range_lanczosBasis hM ▸ LinearMap.mem_range_self _ y)

/-- Let $H$ be symmetric, $M$ positive definite and $k \le \operatorname{grade}(M^{-1}H, M^{-1}g)$.
If $\bar{s}$ is a global minimizer of the reduced problem (10.1.6), then $Q_k \bar{s}$ minimizes
the regularized model $\langle M^{-1}g, s \rangle_M + \frac12 \langle s, M^{-1}H s \rangle_M +
\frac{\sigma}{r} \|s\|_M^r$ of the $M$-inner product space over $\mathcal{K}_k$. -/
theorem isMinOn_krylov_of_reduced (hH : H.IsHermitian) (hM : M.PosDef) {σ r : ℝ} {k : ℕ}
    (hk : k ≤ gradeHM H M g) {sbar : EuclideanSpace ℝ (Fin k)}
    (hs : IsRegularizationSolution (lanczosGrad hM H g k) (lanczosTridiag hM H g k) 1 σ r sbar) :
    IsMinOn (Subproblem.regModel (scaledGrad hM g) (scaledOp H hM) σ r)
      (Krylov.subspace (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)
        (scaledGrad hM g) k : Set (ScaledSpace hM))
      (toScaled hM (toEuclideanLin (lanczosBasis hM H g k) sbar)) :=
  ((isRegSubspaceSolution_iff_scaled hM).1
    ((isRegSubspaceSolution_krylov_iff hM hH hk σ r sbar).2 hs)).2

/-- For a positive definite $M$, every $s \in \mathbb{R}^n$ and every $\lambda \in \mathbb{R}$,
$$\|g + H s + \lambda M s\|_{M^{-1}} = \|M^{-1}g + M^{-1}H s + \lambda s\|,$$
where the norm on the right is the norm of the $M$-inner product space. This is the norm of the
gradient (8.2.34) of the regularized model. -/
theorem mNorm_inv_gradient (hM : M.PosDef) (s : EuclideanSpace ℝ (Fin n)) (lam : ℝ) :
    mNorm M⁻¹ (g + toEuclideanLin H s + lam • toEuclideanLin M s) =
      ‖scaledGrad hM g + scaledOp H hM (toScaled hM s) + lam • toScaled hM s‖ := by
  rw [mNorm_inv_eq_norm_scaledGrad hM, scaledGrad_gradient, _root_.add_apply,
    _root_.smul_apply, one_apply_eq_self, add_assoc]

end Scaled

/-! ### Optimality of the subspace solution (§10.2.1) -/

/-- **Equations (10.2.2)–(10.2.3)** of [cartis2022evaluation]. Let $H \in \mathbb{R}^{n \times n}$
be symmetric, $M \in \mathbb{R}^{n \times n}$ positive definite, $\sigma > 0$, $r > 2$ and $1
\le k \le \operatorname{grade}(M^{-1}H, M^{-1}g)$. Let $\bar{s}_k \in \mathbb{R}^k$ be a global
minimizer of the reduced problem (10.1.6), and let $\lambda_k = \sigma \|\bar{s}_k\|^{r-2}$.
Then
$$(T_k + \lambda_k I_k) \bar{s}_k = -\gamma_1 e_1, \qquad \gamma_1 = \|g\|_{M^{-1}},$$
and $\lambda_k = \sigma \|Q_k \bar{s}_k\|_M^{r-2}$ (10.2.3). Moreover $T_k + \lambda_k I_k$ is
positive definite, so the hard case cannot occur in the subspace, and $\bar{s}_k$ is the unique
global minimizer of (10.1.6).

The norm $\|\bar{s}_k\|$ is the Euclidean norm of $\mathbb{R}^k$, and $e_1$ is
`EuclideanSpace.single ⟨0, hk1⟩ 1`. -/
theorem subspace_optimality_10_2_2 (hH : H.IsHermitian) (hM : M.PosDef) {σ r : ℝ} (hσ : 0 < σ)
    (hr : 2 < r) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ gradeHM H M g)
    {sbar : EuclideanSpace ℝ (Fin k)}
    (hs : IsRegularizationSolution (lanczosGrad hM H g k) (lanczosTridiag hM H g k) 1 σ r sbar) :
    toEuclideanLin (lanczosTridiag hM H g k + (σ * ‖sbar‖ ^ (r - 2)) • (1 : Matrix _ _ ℝ)) sbar =
        -EuclideanSpace.single ⟨0, hk1⟩ (mNorm M⁻¹ g) ∧
      σ * ‖sbar‖ ^ (r - 2) = σ * mNorm M (toEuclideanLin (lanczosBasis hM H g k) sbar) ^ (r - 2) ∧
      (lanczosTridiag hM H g k + (σ * ‖sbar‖ ^ (r - 2)) • (1 : Matrix _ _ ℝ)).PosDef ∧
      ∀ u, IsRegularizationSolution (lanczosGrad hM H g k) (lanczosTridiag hM H g k) 1 σ r u →
        u = sbar := by
  obtain ⟨h1, -, h3⟩ := theorem_8_2_8 (lanczosTridiag_isHermitian hM k) PosDef.one hσ hr hs
  rw [mNorm_one, lanczosGrad_eq hM hk1] at h1
  rw [mNorm_one] at h3
  have hpd : (lanczosTridiag hM H g k + (σ * ‖sbar‖ ^ (r - 2)) • (1 : Matrix _ _ ℝ)).PosDef := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have hT := isSymmetric_scaledOp (hM := hM) hH
    have hb := ne_zero_of_le_gradeHM hM hk1 hk
    have hmin := isMinOn_krylov_of_reduced hH hM hk hs
    have hlt := (neg_leftmost_lt_of_isMinOn_regModel_krylov hT hb hσ hr hk1
      (toScaled_lanczosBasis_mem hM sbar) hmin).1
    rw [← mNorm_eq_norm_toScaled hM, mNorm_lanczosBasis hM hk] at hlt
    exact posDef_tridiag_add hT hb (by rw [← gradeHM_eq hM]; exact hk) hlt
  exact ⟨h1, by rw [mNorm_lanczosBasis hM hk], hpd, h3 hpd⟩

/-! ### Factorizing and solving shifted Lanczos systems (Algorithms 10.2.1–10.2.2) -/

section Algorithms

variable (ρ γ : ℕ → ℝ) (lam : ℝ)

/-- The reciprocal pivots $r_i(\lambda)$ of Algorithm 10.2.1 of [cartis2022evaluation]:
$r_1 = 1/(\rho_1 + \lambda)$ and $r_{i+1} = 1/(\rho_{i+1} + \lambda - \gamma_{i+1} l_{i+1})$
with $l_{i+1} = \gamma_{i+1} r_i$.

The index is $0$-based: the book's $r_{i+1}$, $\rho_{i+1}$ and $\gamma_{i+1}$ are
`recipPivot ρ γ lam i`, `ρ i` and `γ i`. A vanishing denominator gives the value $0$, by the Lean
convention $1/0 = 0$. -/
noncomputable def recipPivot : ℕ → ℝ
  | 0 => 1 / (ρ 0 + lam)
  | i + 1 => 1 / (ρ (i + 1) + lam - γ (i + 1) * (γ (i + 1) * recipPivot i))

/-- The tests of Algorithm 10.2.1 of [cartis2022evaluation]: $\rho_1 + \lambda > 0$ for the first
row, and $\rho_{i+1} + \lambda > \gamma_{i+1} l_{i+1}$ with
$l_{i+1} = \gamma_{i+1} r_i(\lambda)$ for the later rows. The index is $0$-based, as in
`CartisGouldToint.Chapter10.recipPivot`. -/
def pivotTest : ℕ → Prop
  | 0 => 0 < ρ 0 + lam
  | i + 1 => γ (i + 1) * (γ (i + 1) * recipPivot ρ γ lam i) < ρ (i + 1) + lam

/-- The extension by zero of a vector $v \in \mathbb{R}^k$ to a sequence: the value at $j$ is $v_j$
for $j < k$ and $0$ otherwise. -/
def extendFin {k : ℕ} (v : Fin k → ℝ) (j : ℕ) : ℝ := if h : j < k then v ⟨j, h⟩ else 0

omit ρ γ lam in
/-- The extension by zero `CartisGouldToint.Chapter10.extendFin v` agrees with $v$ at every index
$i < k$. -/
@[simp]
theorem extendFin_val {k : ℕ} (v : Fin k → ℝ) (i : Fin k) : extendFin v i = v i := by
  simp [extendFin]

/-- **Algorithm 10.2.1** of [cartis2022evaluation]. Let $T_k$ be the symmetric tridiagonal matrix
with diagonal $\rho_1, \dots, \rho_k$ and off-diagonal $\gamma_2, \dots, \gamma_k$, and let
$\lambda \in \mathbb{R}$. The algorithm factorizes $T_k + \lambda I_k$. It exits with "not
positive definite" as soon as one of the tests `CartisGouldToint.Chapter10.pivotTest` fails for
a row $i \le k$. Otherwise it returns the multipliers $l_i = \gamma_i r_{i-1}$ for
$2 \le i \le k$ and the reciprocal pivots $r_i$ for $1 \le i \le k$.

The exit "not positive definite" is `none`. The matrix $T_k$ is `Matrix.symTridiag ρ γ k`, with
$0$-based indices: `ρ i` and `γ i` are $\rho_{i+1}$ and $\gamma_{i+1}$. The unused multiplier
$l_1$ is set to $0$. -/
noncomputable def algorithm_10_2_1 (k : ℕ) : Option ((Fin k → ℝ) × (Fin k → ℝ)) :=
  open Classical in
  if ∀ i < k, pivotTest ρ γ lam i then
    some (fun i => if (i : ℕ) = 0 then 0 else γ i * recipPivot ρ γ lam (i - 1),
      fun i => recipPivot ρ γ lam i)
  else none

/-- The reciprocal pivots of Algorithm 10.2.1 are the reciprocals of the pivots of the $LDL^T$
factorization of $T_k + \lambda I_k$ (`Matrix.ldlPivot`). -/
theorem recipPivot_eq (i : ℕ) : recipPivot ρ γ lam i = (ldlPivot ρ γ lam i)⁻¹ := by
  induction i with
  | zero => rw [recipPivot, ldlPivot_zero, one_div]
  | succ i ih =>
    rw [recipPivot, ih, ldlPivot_succ, one_div]
    congr 1
    ring

/-- The test of Algorithm 10.2.1 for a row holds if and only if the corresponding pivot of the
$LDL^T$ factorization of $T_k + \lambda I_k$ (`Matrix.ldlPivot`) is positive. -/
theorem pivotTest_iff (i : ℕ) : pivotTest ρ γ lam i ↔ 0 < ldlPivot ρ γ lam i := by
  cases i with
  | zero => rfl
  | succ i =>
    rw [pivotTest, recipPivot_eq, ldlPivot_succ]
    have : γ (i + 1) * (γ (i + 1) * (ldlPivot ρ γ lam i)⁻¹) =
        γ (i + 1) ^ 2 / ldlPivot ρ γ lam i := by ring
    rw [this, sub_pos]

/-- **Algorithm 10.2.1** of [cartis2022evaluation], correctness ((10.2.5)–(10.2.6),
§10.2.1–§10.2.2). Let $T_m$ be the symmetric tridiagonal matrix with diagonal
$\rho_1, \dots, \rho_m$ and off-diagonal $\gamma_2, \dots, \gamma_m$, and let
$\lambda \in \mathbb{R}$.

1. Algorithm 10.2.1 exits with "not positive definite" if and only if $T_k + \lambda I_k$ is not
   positive definite.
2. If it returns $(l, r)$, then $T_k + \lambda I_k = L_k D_k L_k^T$, where $L_k$ is unit lower
   bidiagonal with subdiagonal entries $l_2, \dots, l_k$ and
   $D_k = \operatorname{diag}(1/r_1, \dots, 1/r_k)$, and every entry $1/r_i$ is positive.
3. For $m \ge 1$, if $T_m + \lambda I_m$ is positive definite, then $T_{m+1} + \lambda I_{m+1}$
   is positive definite if and only if $\rho_{m+1} + \lambda > \gamma_{m+1}^2 r_m(\lambda)$.

The matrix $L_k$ is `Matrix.lowerBidiagonalOf` of the multipliers extended by zero. In the Lean
statement, part 3 has $m = k + 1$, and `ρ (k + 1)`, `γ (k + 1)` and `recipPivot ρ γ lam k` are
$\rho_{m+1}$, $\gamma_{m+1}$ and $r_m(\lambda)$. -/
theorem algorithm_10_2_1_spec (k : ℕ) :
    (algorithm_10_2_1 ρ γ lam k = none ↔
      ¬ (symTridiag ρ γ k + lam • (1 : Matrix (Fin k) (Fin k) ℝ)).PosDef) ∧
    (∀ l r, algorithm_10_2_1 ρ γ lam k = some (l, r) →
      symTridiag ρ γ k + lam • (1 : Matrix (Fin k) (Fin k) ℝ) =
          lowerBidiagonalOf (extendFin l) k * diagonal (fun i => (r i)⁻¹) *
            (lowerBidiagonalOf (extendFin l) k)ᵀ ∧
        ∀ i, 0 < (r i)⁻¹) ∧
    ((symTridiag ρ γ (k + 1) + lam • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)).PosDef →
      ((symTridiag ρ γ (k + 2) + lam • (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ)).PosDef ↔
        γ (k + 1) ^ 2 * recipPivot ρ γ lam k < ρ (k + 1) + lam)) := by
  have hpd : (symTridiag ρ γ k + lam • (1 : Matrix (Fin k) (Fin k) ℝ)).PosDef ↔
      ∀ i < k, pivotTest ρ γ lam i := by
    rw [posDef_symTridiag_add_iff]
    exact forall₂_congr fun i _ => (pivotTest_iff ρ γ lam i).symm
  refine ⟨?_, fun l r hlr => ?_, fun h => ?_⟩
  · rw [hpd, algorithm_10_2_1]
    split_ifs with h
    · exact iff_of_false (by simp) (not_not.2 h)
    · exact iff_of_true rfl h
  · rw [algorithm_10_2_1] at hlr
    split_ifs at hlr with ht
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hlr)
    have hd : ∀ i < k, 0 < ldlPivot ρ γ lam i := fun i hi => (pivotTest_iff ρ γ lam i).1 (ht i hi)
    have hL : lowerBidiagonalOf (extendFin fun i : Fin k =>
        if (i : ℕ) = 0 then 0 else γ i * recipPivot ρ γ lam (i - 1)) k = ldlLower ρ γ lam k := by
      rw [ldlLower_eq]
      ext i j
      simp only [lowerBidiagonalOf, of_apply, extendFin_val]
      by_cases h1 : i = j
      · simp [h1]
      by_cases h2 : (j : ℕ) + 1 = i
      · have h3 : (i : ℕ) ≠ 0 := by omega
        obtain ⟨m, hm⟩ : ∃ m, (i : ℕ) = m + 1 := ⟨i - 1, by omega⟩
        simp only [h1, h2, h3, ite_false, ite_true]
        rw [hm, ldlMult_succ, Nat.add_sub_cancel, recipPivot_eq, div_eq_mul_inv]
      · simp [h1, h2]
    refine ⟨?_, fun i => by
      change 0 < (recipPivot ρ γ lam i)⁻¹
      rw [recipPivot_eq, inv_inv]; exact hd i i.2⟩
    have hD : (fun i : Fin k => ((fun i : Fin k => recipPivot ρ γ lam i) i)⁻¹) =
        fun i : Fin k => ldlPivot ρ γ lam i := funext fun i => by
      change (recipPivot ρ γ lam i)⁻¹ = _
      rw [recipPivot_eq, inv_inv]
    rw [hL, hD, symTridiag_add_smul_one_eq_ldl ρ γ lam fun i hi => (hd i (by omega)).ne']
  · rw [posDef_symTridiag_succ_add_iff ρ γ lam h, recipPivot_eq, div_eq_mul_inv]

/-- The forward substitution of Algorithm 10.2.2 of [cartis2022evaluation]: $x_1 = b_1$ and
$x_{i+1} = b_{i+1} - l_{i+1} x_i$, with $b$ and $l$ extended by zero beyond $k$. The index is
$0$-based. -/
noncomputable def solveForward {k : ℕ} (l b : Fin k → ℝ) : ℕ → ℝ
  | 0 => extendFin b 0
  | i + 1 => extendFin b (i + 1) - extendFin l (i + 1) * solveForward l b i

/-- The backward substitution of Algorithm 10.2.2 of [cartis2022evaluation]: the last entry
$x_k = z_k$ is unchanged, and $x_i = z_i - l_{i+1} x_{i+1}$ for $i < k$. The index is $0$-based,
and every index $i \ge k - 1$ gives $z_i$. -/
noncomputable def solveBackward (k : ℕ) (l' z : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i + 1 < k then z i - l' (i + 1) * solveBackward k l' z (i + 1) else z i
termination_by k - i

/-- The recursion equation of the backward substitution `CartisGouldToint.Chapter10.solveBackward`:
the value at $i$ is $z_i - l_{i+1} x_{i+1}$ if $i + 1 < k$, and $z_i$ otherwise. -/
theorem solveBackward_eq (k : ℕ) (l' z : ℕ → ℝ) (i : ℕ) :
    solveBackward k l' z i =
      if i + 1 < k then z i - l' (i + 1) * solveBackward k l' z (i + 1) else z i := by
  rw [solveBackward]

/-- **Algorithm 10.2.2** of [cartis2022evaluation]. Given the factors $l$ and $r$ that Algorithm
10.2.1 returns for $T_k + \lambda I_k$ and a vector $b \in \mathbb{R}^k$, the algorithm computes
$x$ by the forward substitution $x_i \leftarrow b_i - l_i x_{i-1}$, the scaling
$x_i \leftarrow r_i x_i$, and the backward substitution $x_{i-1} \leftarrow x_{i-1} - l_i x_i$. -/
noncomputable def algorithm_10_2_2 {k : ℕ} (l r b : Fin k → ℝ) : Fin k → ℝ :=
  fun i => solveBackward k (extendFin l) (fun j => extendFin r j * solveForward l b j) i

/-- **Algorithm 10.2.2** of [cartis2022evaluation], correctness ((10.2.4)). If Algorithm 10.2.1
returns the factors $(l, r)$ of $T_k + \lambda I_k$, then for every $b \in \mathbb{R}^k$ the
output $x$ of Algorithm 10.2.2 satisfies $(T_k + \lambda I_k) x = b$. -/
theorem algorithm_10_2_2_spec {k : ℕ} {l r : Fin k → ℝ}
    (h : algorithm_10_2_1 ρ γ lam k = some (l, r)) (b : Fin k → ℝ) :
    (symTridiag ρ γ k + lam • (1 : Matrix (Fin k) (Fin k) ℝ)) *ᵥ algorithm_10_2_2 l r b = b := by
  rw [algorithm_10_2_1] at h
  split_ifs at h with ht
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have hd : ∀ i < k, 0 < ldlPivot ρ γ lam i := fun i hi => (pivotTest_iff ρ γ lam i).1 (ht i hi)
  set l : Fin k → ℝ := fun i => if (i : ℕ) = 0 then 0 else γ i * recipPivot ρ γ lam (i - 1)
  have hl : ∀ i, 1 ≤ i → i < k → extendFin l i = ldlMult ρ γ lam i := fun i hi1 hik => by
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    simp only [extendFin, hik, dite_true, l, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      ite_false, Nat.add_sub_cancel]
    rw [ldlMult_succ, recipPivot_eq, div_eq_mul_inv]
  have hf : ∀ j < k, solveForward l b j =
      ldlForward ρ γ lam (fun j => if h : j < k then b ⟨j, h⟩ else 0) j := by
    intro j hj
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [solveForward, ldlForward, ih (by omega), hl _ (by omega) hj]
      rfl
  have hb : ∀ m i, i + m + 1 = k →
      solveBackward k (extendFin l) (fun j => extendFin (fun i : Fin k => recipPivot ρ γ lam i) j *
          solveForward l b j) i =
        ldlBackward ρ γ lam k (fun j => ldlForward ρ γ lam
          (fun j => if h : j < k then b ⟨j, h⟩ else 0) j / ldlPivot ρ γ lam j) i := by
    have hz : ∀ j < k, extendFin (fun i : Fin k => recipPivot ρ γ lam i) j * solveForward l b j =
        ldlForward ρ γ lam (fun j => if h : j < k then b ⟨j, h⟩ else 0) j / ldlPivot ρ γ lam j :=
      fun j hj => by
        simp only [extendFin, hj, dite_true]
        rw [hf j hj, recipPivot_eq, div_eq_mul_inv, mul_comm]
    intro m
    induction m with
    | zero =>
      intro i hi
      rw [solveBackward_eq, ldlBackward_eq, ite_eq_right (by omega), ite_eq_right (by omega)]
      exact hz i (by omega)
    | succ m ih =>
      intro i hi
      rw [solveBackward_eq, ldlBackward_eq, ite_eq_left (by omega), ite_eq_left (by omega),
        ih (i + 1) (by omega), hz i (by omega), hl _ (by omega) (by omega)]
  have heq : algorithm_10_2_2 l (fun i => recipPivot ρ γ lam i) b = tridiagSolve ρ γ lam k b := by
    funext i
    exact hb (k - 1 - i) i (by omega)
  rw [heq]
  exact mulVec_tridiagSolve ρ γ lam (fun i hi => (hd i hi).ne') b

end Algorithms

/-! ### Monotonicity (Lemma 10.2.1) and the start (§10.2.3) -/

/-- **Lemma 10.2.1** of [cartis2022evaluation] (nested subspace solutions increase in norm). Let
$H \in \mathbb{R}^{n \times n}$ be symmetric, $M \in \mathbb{R}^{n \times n}$ positive definite,
$\sigma > 0$, $r > 2$ and $1 \le k \le \ell \le \operatorname{grade}(M^{-1}H, M^{-1}g)$. Let
$\bar{s}_k$ and $\bar{s}_\ell$ be global minimizers of the reduced problems (10.1.6) of
dimensions $k$ and $\ell$, let $s_k = Q_k \bar{s}_k$ and $s_\ell = Q_\ell \bar{s}_\ell$, and let
$s_*$ be a global minimizer of the regularization subproblem (8.1.3). With the multipliers
$\lambda_k = \sigma \|s_k\|_M^{r-2}$, $\lambda_\ell = \sigma \|s_\ell\|_M^{r-2}$ (10.2.3) and
$\lambda_* = \sigma \|s_*\|_M^{r-2}$,
$$\lambda_k \le \lambda_\ell \le \lambda_* \quad\text{and}\quad \|s_k\|_M \le \|s_\ell\|_M \le
  \|s_*\|_M.$$

**Typo.** The source refers to "a global minimizer of (8.1.4)". (8.1.4) is the regularized
model; the problem is (8.1.3). -/
theorem lemma_10_2_1 (hH : H.IsHermitian) (hM : M.PosDef) {σ r : ℝ} (hσ : 0 < σ) (hr : 2 < r)
    {k ℓ : ℕ} (hk : 1 ≤ k) (hkℓ : k ≤ ℓ) (hℓ : ℓ ≤ gradeHM H M g)
    {sbark : EuclideanSpace ℝ (Fin k)} {sbarl : EuclideanSpace ℝ (Fin ℓ)}
    (hsk : IsRegularizationSolution (lanczosGrad hM H g k) (lanczosTridiag hM H g k) 1 σ r sbark)
    (hsl : IsRegularizationSolution (lanczosGrad hM H g ℓ) (lanczosTridiag hM H g ℓ) 1 σ r sbarl)
    {sstar : EuclideanSpace ℝ (Fin n)} (hstar : IsRegularizationSolution g H M σ r sstar) :
    (σ * mNorm M (toEuclideanLin (lanczosBasis hM H g k) sbark) ^ (r - 2) ≤
        σ * mNorm M (toEuclideanLin (lanczosBasis hM H g ℓ) sbarl) ^ (r - 2) ∧
      σ * mNorm M (toEuclideanLin (lanczosBasis hM H g ℓ) sbarl) ^ (r - 2) ≤
        σ * mNorm M sstar ^ (r - 2)) ∧
    mNorm M (toEuclideanLin (lanczosBasis hM H g k) sbark) ≤
        mNorm M (toEuclideanLin (lanczosBasis hM H g ℓ) sbarl) ∧
      mNorm M (toEuclideanLin (lanczosBasis hM H g ℓ) sbarl) ≤ mNorm M sstar := by
  simp only [mNorm_eq_norm_toScaled hM]
  exact krylov_multiplier_mono_regularization (isSymmetric_scaledOp hH) hσ hr hk hkℓ
    (toScaled_lanczosBasis_mem hM sbark) (isMinOn_krylov_of_reduced hH hM (hkℓ.trans hℓ) hsk)
    (toScaled_lanczosBasis_mem hM sbarl) (isMinOn_krylov_of_reduced hH hM hℓ hsl)
    ((isRegularizationSolution_iff_scaled hM).1 hstar)

/-- **Equation (10.2.7)** of [cartis2022evaluation], the start of the Lanczos process (§10.2.3). For
$k = 1$ the reduced problem (10.1.6) is
$$\min_{s \in \mathbb{R}} \; \gamma_1 s + \tfrac12 \rho_1 s^2 + \tfrac1r \sigma |s|^r.$$
Let $\gamma_1, \rho_1 \in \mathbb{R}$ with $\gamma_1 \neq 0$, let $\sigma > 0$ and $r > 2$, and
let $\bar{s}_1$ be a global minimizer of this problem, with the multiplier
$\lambda_1 = \sigma |\bar{s}_1|^{r-2}$. Then $\gamma_1 + (\rho_1 + \lambda_1) \bar{s}_1 = 0$
(10.2.7), $\rho_1 + \lambda_1 > 0$ and $\lambda_1 > 0$. The multiplier $\lambda_1$ satisfies the
rearranged secular equation
$$\lambda (\rho_1 + \lambda)^{r-2} = \sigma |\gamma_1|^{r-2},$$
and it is the only root of this equation with $\lambda > \max(0, -\rho_1)$. For $r = 3$,
$\lambda_1 = \bigl(-\rho_1 + \sqrt{\rho_1^2 + 4 \sigma |\gamma_1|}\bigr)/2$, the larger root of
a quadratic. -/
theorem start_10_2_3 {γ₁ ρ₁ σ r : ℝ} (hγ : γ₁ ≠ 0) (hσ : 0 < σ) (hr : 2 < r) {s : ℝ}
    (hs : ∀ u : ℝ, γ₁ * s + 1 / 2 * ρ₁ * s ^ 2 + 1 / r * σ * |s| ^ r ≤
      γ₁ * u + 1 / 2 * ρ₁ * u ^ 2 + 1 / r * σ * |u| ^ r) :
    γ₁ + (ρ₁ + σ * |s| ^ (r - 2)) * s = 0 ∧ 0 < ρ₁ + σ * |s| ^ (r - 2) ∧
      0 < σ * |s| ^ (r - 2) ∧
      σ * |s| ^ (r - 2) * (ρ₁ + σ * |s| ^ (r - 2)) ^ (r - 2) = σ * |γ₁| ^ (r - 2) ∧
      (∀ μ, max 0 (-ρ₁) < μ → μ * (ρ₁ + μ) ^ (r - 2) = σ * |γ₁| ^ (r - 2) →
        μ = σ * |s| ^ (r - 2)) ∧
      (r = 3 → σ * |s| ^ (r - 2) = (-ρ₁ + √(ρ₁ ^ 2 + 4 * σ * |γ₁|)) / 2) := by
  set T : ℝ →L[ℝ] ℝ := ρ₁ • (1 : ℝ →L[ℝ] ℝ)
  have hT : (T : ℝ →ₗ[ℝ] ℝ).IsSymmetric := fun x y => by
    simp only [T, ContinuousLinearMap.coe_coe, _root_.smul_apply, one_apply_eq_self,
      real_inner_smul_left, real_inner_smul_right]
  have hmin : IsMinOn (Subproblem.regModel γ₁ T σ r) univ s := isMinOn_univ_iff.2 fun u => by
    have := hs u
    simp only [Subproblem.regModel_def, quadModel_def, T, _root_.smul_apply, one_apply_eq_self,
      Real.norm_eq_abs, RCLike.inner_apply, conj_trivial, smul_eq_mul]
    calc _ = γ₁ * s + 1 / 2 * ρ₁ * s ^ 2 + 1 / r * σ * |s| ^ r := by ring
      _ ≤ _ := this
      _ = _ := by ring
  obtain ⟨h1, h2⟩ := (isMinOn_regModel_iff hT hσ hr).1 hmin
  simp only [T, _root_.add_apply, _root_.smul_apply, one_apply_eq_self, smul_eq_mul,
    Real.norm_eq_abs] at h1
  set lam := σ * |s| ^ (r - 2) with hlam
  have hshift : γ₁ + (ρ₁ + lam) * s = 0 := by linarith
  have hs0 : s ≠ 0 := by rintro rfl; apply hγ; linarith
  have hlam0 : 0 < lam := mul_pos hσ (Real.rpow_pos_of_pos (abs_pos.2 hs0) _)
  have hpos : 0 ≤ ρ₁ + lam := by
    have := h2.inner_nonneg_left 1
    simp only [ContinuousLinearMap.coe_coe, T, _root_.add_apply, _root_.smul_apply,
      one_apply_eq_self, smul_eq_mul, RCLike.inner_apply, conj_trivial, Real.norm_eq_abs] at this
    linarith [hlam]
  have hpos' : 0 < ρ₁ + lam := by
    refine lt_of_le_of_ne hpos fun h => hγ ?_
    rw [← h, zero_mul, add_zero] at hshift; exact hshift
  have habs : |γ₁| = (ρ₁ + lam) * |s| := by
    rw [show γ₁ = -((ρ₁ + lam) * s) by linarith, abs_neg, abs_mul, abs_of_pos hpos']
  have hroot : lam * (ρ₁ + lam) ^ (r - 2) = σ * |γ₁| ^ (r - 2) := by
    rw [habs, Real.mul_rpow hpos'.le (abs_nonneg _), hlam]; ring
  have hmono : ∀ a b, max 0 (-ρ₁) < a → a < b →
      a * (ρ₁ + a) ^ (r - 2) < b * (ρ₁ + b) ^ (r - 2) := by
    intro a b ha hab
    have ha0 : 0 < a := lt_of_le_of_lt (le_max_left _ _) ha
    have hρa : 0 < ρ₁ + a := by have := lt_of_le_of_lt (le_max_right _ _) ha; linarith
    have h3 : (ρ₁ + a) ^ (r - 2) ≤ (ρ₁ + b) ^ (r - 2) :=
      Real.rpow_le_rpow hρa.le (by linarith) (by linarith)
    have h4 : 0 < (ρ₁ + a) ^ (r - 2) := Real.rpow_pos_of_pos hρa _
    calc a * (ρ₁ + a) ^ (r - 2) < b * (ρ₁ + a) ^ (r - 2) := mul_lt_mul_of_pos_right hab h4
      _ ≤ b * (ρ₁ + b) ^ (r - 2) := mul_le_mul_of_nonneg_left h3 (by linarith)
  have hlamD : max 0 (-ρ₁) < lam := max_lt hlam0 (by linarith)
  refine ⟨hshift, hpos', hlam0, hroot, fun μ hμ hμr => ?_, fun hr3 => ?_⟩
  · rcases lt_trichotomy μ lam with h | h | h
    · exact absurd (hμr.trans hroot.symm) (hmono μ lam hμ h).ne
    · exact h
    · exact absurd (hroot.trans hμr.symm) (hmono lam μ hlamD h).ne
  · rw [hr3, show (3 : ℝ) - 2 = 1 by norm_num, Real.rpow_one, Real.rpow_one] at hroot
    have hsq : ρ₁ ^ 2 + 4 * σ * |γ₁| = (2 * lam + ρ₁) ^ 2 := by nlinarith
    rw [hsq, Real.sqrt_sq (by linarith)]
    ring

/-! ### The gradient bound (Theorem 10.2.2) and the iteration bound (Corollary 10.2.3) -/

/-- **Equation (10.2.8)** of [cartis2022evaluation]. The **condition number** of $T_k + \lambda I_k$
is
$$\kappa_k(\lambda) = \frac{\theta_{k,k} + \lambda}{\theta_{1,k} + \lambda},$$
where $\theta_{1,k} \le \theta_{k,k}$ are the smallest and the largest Ritz values, that is,
eigenvalues of $T_k$. The source evaluates it at the multiplier $\lambda = \lambda_k$.

The Ritz values are `Lanczos.ritzValues` of the operator $M^{-1}H$ in the $M$-inner product
space and the vector $M^{-1}g$. A zero denominator gives the value $0$, by the Lean convention
for division. For $k = 0$ the empty supremum and infimum are $0$. -/
noncomputable def conditionNumber_10_2_8 (hM : M.PosDef) (H : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (lam : ℝ) : ℝ :=
  ((⨆ i, Lanczos.ritzValues (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)
      (scaledGrad hM g) k i) + lam) /
    ((⨅ i, Lanczos.ritzValues (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)
      (scaledGrad hM g) k i) + lam)

/-- **Equation (10.2.10)** of [cartis2022evaluation]. For multipliers $\lambda_k$, the **largest
condition number** is
$$\kappa_* = \max_{1 \le k \le \operatorname{grade}(M^{-1}H, M^{-1}g)} \kappa_k(\lambda_k).$$

The multipliers are a sequence `lam : ℕ → ℝ`. If the grade is $0$, the supremum is over the
empty set and equals $0$. -/
noncomputable def kappaStar (hM : M.PosDef) (H : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (lam : ℕ → ℝ) : ℝ :=
  ⨆ k : Finset.Icc 1 (gradeHM H M g), conditionNumber_10_2_8 hM H g k (lam k)

/-- Let $H$ be symmetric and $M$ positive definite. For
$k \le \operatorname{grade}(M^{-1}H, M^{-1}g)$ and every $\lambda$, the condition number
$\kappa_k(\lambda)$ of (10.2.8) equals `Subproblem.krylovCond`, the ratio $(\lambda_{\max} +
\lambda)/(\lambda_{\min} + \lambda)$ for the extreme eigenvalues of the compression of $M^{-1}H$
to $\mathcal{K}_k$. -/
theorem conditionNumber_eq_krylovCond (hH : H.IsHermitian) (hM : M.PosDef) {k : ℕ}
    (hk : k ≤ gradeHM H M g) (lam : ℝ) :
    conditionNumber_10_2_8 hM H g k lam =
      krylovCond (isSymmetric_scaledOp hH) (scaledGrad hM g) k lam := by
  rw [krylovCond_eq_ritzValues _ (by rw [← gradeHM_eq hM]; exact hk), conditionNumber_10_2_8]

/-- For every sequence of multipliers $\lambda_k$ and every $1 \le k \le
\operatorname{grade}(M^{-1}H, M^{-1}g)$, $\kappa_k(\lambda_k) \le \kappa_*$. -/
theorem le_kappaStar (hM : M.PosDef) (lam : ℕ → ℝ) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k ≤ gradeHM H M g) :
    conditionNumber_10_2_8 hM H g k (lam k) ≤ kappaStar hM H g lam :=
  le_ciSup (f := fun k : Finset.Icc 1 (gradeHM H M g) => conditionNumber_10_2_8 hM H g k (lam k))
    (Finite.bddAbove_range _) ⟨k, Finset.mem_Icc.2 ⟨hk1, hk⟩⟩

/-- **Theorem 10.2.2** of [cartis2022evaluation] (bound on the gradient at the subspace minimizer).
Let $H \in \mathbb{R}^{n \times n}$ be symmetric, $M \in \mathbb{R}^{n \times n}$ positive
definite, $\sigma > 0$, $r > 2$ and $1 \le k \le \operatorname{grade}(M^{-1}H, M^{-1}g)$. Let
$\bar{s}_k$ be a global minimizer of the reduced problem (10.1.6), let $s_k = Q_k \bar{s}_k$,
let $\lambda_k = \sigma \|s_k\|_M^{r-2}$ (10.2.3), and let $\kappa_k = \kappa_k(\lambda_k)$ be
the condition number (10.2.8). Then the gradient $\nabla_s m^R(s_k) = g + H s_k + \lambda_k M
s_k$ of (8.2.34) satisfies (10.2.9):
$$\|\nabla_s m^R(s_k)\|_{M^{-1}} \le 2 \|M^{-1}H\| \, \kappa_k
  \Bigl(\frac{\lambda_k}{\sigma}\Bigr)^{1/(r-2)} \Bigl(\frac{\sqrt{\kappa_k} -
  1}{\sqrt{\kappa_k} + 1}\Bigr)^{k-1}.$$

The norm $\|M^{-1}H\|$ is the operator norm induced by $\|\cdot\|_M$, the norm of
`Subproblem.scaledOp H hM`. -/
theorem theorem_10_2_2 (hH : H.IsHermitian) (hM : M.PosDef) {σ r : ℝ} (hσ : 0 < σ) (hr : 2 < r)
    {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ gradeHM H M g) {sbar : EuclideanSpace ℝ (Fin k)}
    (hs : IsRegularizationSolution (lanczosGrad hM H g k) (lanczosTridiag hM H g k) 1 σ r sbar) :
    mNorm M⁻¹ (g + toEuclideanLin H (toEuclideanLin (lanczosBasis hM H g k) sbar) +
        (σ * mNorm M (toEuclideanLin (lanczosBasis hM H g k) sbar) ^ (r - 2)) •
          toEuclideanLin M (toEuclideanLin (lanczosBasis hM H g k) sbar)) ≤
      2 * ‖scaledOp H hM‖ *
        conditionNumber_10_2_8 hM H g k
          (σ * mNorm M (toEuclideanLin (lanczosBasis hM H g k) sbar) ^ (r - 2)) *
        (σ * mNorm M (toEuclideanLin (lanczosBasis hM H g k) sbar) ^ (r - 2) / σ) ^ (1 / (r - 2)) *
        ((√(conditionNumber_10_2_8 hM H g k
            (σ * mNorm M (toEuclideanLin (lanczosBasis hM H g k) sbar) ^ (r - 2))) - 1) /
          (√(conditionNumber_10_2_8 hM H g k
            (σ * mNorm M (toEuclideanLin (lanczosBasis hM H g k) sbar) ^ (r - 2))) + 1)) ^
          (k - 1) := by
  have hT := isSymmetric_scaledOp (hM := hM) hH
  have hb := ne_zero_of_le_gradeHM hM hk1 hk
  have hmem := toScaled_lanczosBasis_mem (H := H) (g := g) hM sbar
  have hmin := isMinOn_krylov_of_reduced hH hM hk hs
  have hbound := krylov_gradient_bound_regularization hT hb hσ hr hk1 hmem hmin
  rw [mNorm_inv_gradient hM, mNorm_eq_norm_toScaled hM, conditionNumber_eq_krylovCond hH hM hk]
  exact hbound

/-- **Corollary 10.2.3** of [cartis2022evaluation] (iteration bound for the subspace approximation).
Let $H \in \mathbb{R}^{n \times n}$ be symmetric, $M \in \mathbb{R}^{n \times n}$ positive
definite, $g \neq 0$, $\sigma > 0$, $r > 2$ and $\theta_1 > 0$. For every $1 \le k \le
\operatorname{grade}(M^{-1}H, M^{-1}g)$ let $\bar{s}_k$ be a global minimizer of the reduced
problem (10.1.6), let $s_k = Q_k \bar{s}_k$ and $\lambda_k = \sigma \|s_k\|_M^{r-2}$. Let $s_*$
be a global minimizer of the regularization subproblem (8.1.3), and
$\lambda_* = \sigma \|s_*\|_M^{r-2}$. Let $\kappa_*$ be the largest condition number (10.2.10),
$\lambda_{\max}[H, M]$ the largest eigenvalue of the pencil $(H, M)$, and
$$A = \frac{4 \|M^{-1}H\| \kappa_*}{\theta_1} \Bigl(\frac{\lambda_*}{\sigma}\Bigr)^{1/(r-2)}
  \Bigl(\frac{\lambda_{\max}[H, M] + \lambda_*}{\|g\|_{M^{-1}}}\Bigr)^2.$$
If $\kappa_* > 1$, the stopping rule (9.3.14b)
$$\|g + H s_k + \lambda_k M s_k\|_{M^{-1}} \le \tfrac12 \theta_1 \|s_k\|_M^2$$
holds for some $k$ with
$$1 \le k \le \min\Bigl(\Bigl\lceil \frac{\log A}{\log((\sqrt{\kappa_*} + 1)/(\sqrt{\kappa_*} -
  1))} \Bigr\rceil_+ + 1, \; \operatorname{grade}(M^{-1}H, M^{-1}g)\Bigr).$$
If $\kappa_* = 1$, it holds for some $1 \le k \le \min(2, \operatorname{grade}(M^{-1}H,
M^{-1}g))$.

**Correction.** The source prints the bound $\lceil \log A / \log((\sqrt{\kappa_*} +
1)/(\sqrt{\kappa_*} - 1)) \rceil + 1$. This bound cannot be met when $\log A < 0$, for example
for a large $\theta_1$, and it is undefined for $\kappa_* = 1$. Here the ceiling is
$\lceil x \rceil_+ = \max(\lceil x \rceil, 0)$, the case $\kappa_* = 1$ is stated separately,
and the hypothesis $g \neq 0$, which the proof needs, is added.

The norm $\|M^{-1}H\|$ is the operator norm induced by $\|\cdot\|_M$, and $\lambda_{\max}[H, M]$
is `CartisGouldToint.Chapter09.rightmostPencil`. The logarithm is `Real.log`. -/
theorem corollary_10_2_3 (hH : H.IsHermitian) (hM : M.PosDef) (hg : g ≠ 0) {σ r θ : ℝ}
    (hσ : 0 < σ) (hr : 2 < r) (hθ : 0 < θ) {sbar : (k : ℕ) → EuclideanSpace ℝ (Fin k)}
    (hs : ∀ k, 1 ≤ k → k ≤ gradeHM H M g →
      IsRegularizationSolution (lanczosGrad hM H g k) (lanczosTridiag hM H g k) 1 σ r (sbar k))
    {s : ℕ → EuclideanSpace ℝ (Fin n)}
    (hsk : ∀ k, s k = toEuclideanLin (lanczosBasis hM H g k) (sbar k))
    {sstar : EuclideanSpace ℝ (Fin n)} (hstar : IsRegularizationSolution g H M σ r sstar) :
    (1 < kappaStar hM H g (fun k => σ * mNorm M (s k) ^ (r - 2)) →
      ∃ k, 1 ≤ k ∧
        k ≤ min (⌈Real.log (4 * ‖scaledOp H hM‖ *
            kappaStar hM H g (fun k => σ * mNorm M (s k) ^ (r - 2)) / θ *
            (σ * mNorm M sstar ^ (r - 2) / σ) ^ (1 / (r - 2)) *
            ((rightmostPencil hH hM + σ * mNorm M sstar ^ (r - 2)) / mNorm M⁻¹ g) ^ 2) /
          Real.log ((√(kappaStar hM H g (fun k => σ * mNorm M (s k) ^ (r - 2))) + 1) /
            (√(kappaStar hM H g (fun k => σ * mNorm M (s k) ^ (r - 2))) - 1))⌉₊ + 1)
          (gradeHM H M g) ∧
        mNorm M⁻¹ (g + toEuclideanLin H (s k) +
            (σ * mNorm M (s k) ^ (r - 2)) • toEuclideanLin M (s k)) ≤
          1 / 2 * θ * mNorm M (s k) ^ 2) ∧
    (kappaStar hM H g (fun k => σ * mNorm M (s k) ^ (r - 2)) = 1 →
      ∃ k, 1 ≤ k ∧ k ≤ min 2 (gradeHM H M g) ∧
        mNorm M⁻¹ (g + toEuclideanLin H (s k) +
            (σ * mNorm M (s k) ^ (r - 2)) • toEuclideanLin M (s k)) ≤
          1 / 2 * θ * mNorm M (s k) ^ 2) := by
  have hT := isSymmetric_scaledOp (hM := hM) hH
  have hb := scaledGrad_ne_zero (hM := hM) hg
  set κs := kappaStar hM H g (fun k => σ * mNorm M (s k) ^ (r - 2))
  set G := gradeHM H M g with hGdef
  have hGeq : G = Krylov.grade (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)
      (scaledGrad hM g) := gradeHM_eq hM
  have hG : 1 ≤ G := by rw [hGeq]; exact Krylov.grade_pos_of_ne_zero _ _ hb
  have hS : ∀ k, toScaled hM (s k) ∈
      Krylov.subspace (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g) k :=
    fun k => hsk k ▸ toScaled_lanczosBasis_mem hM (sbar k)
  have hmin : ∀ k, 1 ≤ k → k ≤ Krylov.grade (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] _)
      (scaledGrad hM g) → IsMinOn (Subproblem.regModel (scaledGrad hM g) (scaledOp H hM) σ r)
        (Krylov.subspace (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] _) (scaledGrad hM g) k :
          Set (ScaledSpace hM)) (toScaled hM (s k)) := fun k hk1 hk => by
    rw [← hGeq] at hk
    rw [hsk k]
    exact isMinOn_krylov_of_reduced hH hM hk (hs k hk1 hk)
  have hκs : ∀ k, 1 ≤ k → k ≤ Krylov.grade (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] _)
      (scaledGrad hM g) → krylovCond hT (scaledGrad hM g) k (σ * ‖toScaled hM (s k)‖ ^ (r - 2)) ≤
        κs := fun k hk1 hk => by
    rw [← hGeq] at hk
    rw [← mNorm_eq_norm_toScaled hM, ← conditionNumber_eq_krylovCond hH hM hk]
    exact le_kappaStar hM (fun k => σ * mNorm M (s k) ^ (r - 2)) hk1 hk
  have hκ1 : 1 ≤ κs := by
    refine le_trans ?_ (hκs 1 le_rfl (hGeq ▸ hG))
    exact one_le_krylovCond hT (neg_leftmost_lt_of_isMinOn_regModel_krylov hT hb hσ hr le_rfl
      (hS 1) (hmin 1 le_rfl (hGeq ▸ hG))).1
  obtain ⟨hP, hPG, -, -⟩ := krylov_iteration_bound_regularization hT hb hσ hr hθ hS hmin
    ((isRegularizationSolution_iff_scaled hM).1 hstar) hκs
  rw [← hGeq] at hP hPG
  simp only [← mNorm_eq_norm_toScaled hM, ← rightmostPencil_eq hH hM,
    ← mNorm_inv_eq_norm_scaledGrad hM] at hP hPG
  have htest : ∀ k, ‖scaledGrad hM g + scaledOp H hM (toScaled hM (s k)) +
      (σ * mNorm M (s k) ^ (r - 2)) • toScaled hM (s k)‖ =
      mNorm M⁻¹ (g + toEuclideanLin H (s k) +
        (σ * mNorm M (s k) ^ (r - 2)) • toEuclideanLin M (s k)) := fun k =>
    (mNorm_inv_gradient hM _ _).symm
  simp only [htest] at hP hPG
  set A := 4 * ‖scaledOp H hM‖ * κs / θ *
    (σ * mNorm M sstar ^ (r - 2) / σ) ^ (1 / (r - 2)) *
    ((rightmostPencil hH hM + σ * mNorm M sstar ^ (r - 2)) / mNorm M⁻¹ g) ^ 2
  have hP' : ∀ k, 1 ≤ k → k ≤ G → A * convFactor κs ^ (k - 1) ≤ 1 →
      mNorm M⁻¹ (g + toEuclideanLin H (s k) +
        (σ * mNorm M (s k) ^ (r - 2)) • toEuclideanLin M (s k)) ≤
          1 / 2 * θ * mNorm M (s k) ^ 2 := fun k hk1 hk hA => by
    refine hP k hk1 hk (le_trans ?_ hA)
    have hq := convFactor_nonneg hκ1
    have : 0 ≤ κs := by linarith
    have : 0 ≤ (σ * mNorm M sstar ^ (r - 2) / σ) ^ (1 / (r - 2)) :=
      Real.rpow_nonneg (div_nonneg (mul_nonneg hσ.le
        (Real.rpow_nonneg (mNorm_nonneg _ _) _)) hσ.le) _
    simp only [A]
    gcongr
  obtain ⟨h1, h2⟩ := exists_le_min_of_geometric hG hP' hPG
  refine ⟨fun hκ => ?_, fun hκ => h2 (by rw [hκ, convFactor_one])⟩
  have := h1 (convFactor_pos hκ) (convFactor_lt_one κs)
  rwa [convFactor_def, one_div_div] at this

end CartisGouldToint.Chapter10
