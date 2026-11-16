/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Eigen.KrylovEigen
import Numlib.LinearAlgebra.Matrix.InverseDecay
import Numlib.Optimization.Subproblem.Krylov

/-!
# Convergence of the Krylov subproblem solutions

Let $H$ be a symmetric operator on a finite-dimensional real inner product space, let $g \neq 0$,
and let $s_k$ solve the regularization or trust-region subproblem restricted to the Krylov subspace
$\mathcal{K}_k = \mathcal{K}_k(H, g)$ (see `Numlib.Optimization.Subproblem.Krylov`), with multiplier
$\lambda_k$. This file proves the convergence bounds of Section 10.2.4 and Section 10.3 of
[cartis2022evaluation], which follow Gould and Simoncini. The gradient (for regularization) or the
residual (for the trust region) $g + H s_k + \lambda_k s_k$ decays like $q(\kappa_k)^{k-1}$, where
$$\kappa_k = \frac{\theta_k + \lambda_k}{\theta_1 + \lambda_k}, \qquad q(\kappa) =
  \frac{\sqrt{\kappa} - 1}{\sqrt{\kappa} + 1},$$
and $\kappa_k$ is the condition number of the positive definite matrix $T_k + \lambda_k$, with
$\theta_1 \le \theta_k$ the extreme Ritz values. The file also derives the resulting bounds on the
number of iterations until the stopping tests hold.

## Main definitions

* `Subproblem.krylovCond`: the condition number $\kappa_k(\mu) = (\theta_k + \mu) / (\theta_1 +
  \mu)$ of the compression of $H + \mu$ to $\mathcal{K}_k$, as in (10.2.8).
* `Subproblem.convFactor`: the convergence factor $q(\kappa) = (\sqrt{\kappa} - 1) /
  (\sqrt{\kappa} + 1)$.

## Main results

* `Subproblem.krylov_residual_le`: the residual bound $2 \|H\| \kappa_k \|s_k\| q(\kappa_k)^{k-1}$
  for every point of $\mathcal{K}_k$ that satisfies the restricted first-order condition with a
  shift $\mu > -\theta_1$.
* `Subproblem.krylov_gradient_bound_regularization`: Theorem 10.2.2, the bound on the gradient at
  the minimizer of the regularized model over $\mathcal{K}_k$.
* `Subproblem.krylov_residual_bound_trustRegion`: Theorem 10.3.2, the bound on the residual at the
  trust-region solution over $\mathcal{K}_k$.
* `Subproblem.krylov_iteration_bound_regularization`: Corollary 10.2.3, the number of iterations
  until the stopping rule (9.3.14b) holds.
* `Subproblem.krylov_iteration_bound_trustRegion`: Corollary 10.3.3, the number of iterations until
  the residual test (10.3.2) holds.
* `Subproblem.leftmost_rightmost_compressionL_eq_ritzValues`, `Subproblem.krylovCond_eq_ritzValues`:
  for $k \le \operatorname{grade}(H, g)$, $\theta_1$ and $\theta_k$ are the extreme eigenvalues of
  the Lanczos tridiagonal matrix $T_k$, so $\kappa_k(\mu) = (\lambda_{\max}(T_k) + \mu) /
  (\lambda_{\min}(T_k) + \mu)$.
* `Subproblem.posDef_tridiag_add`, `Subproblem.eigenvalues_tridiag_add_mem`: for $\mu > -\theta_1$,
  the matrix $T_{m+1} + \mu$ is positive definite, with spectrum in
  $[\theta_1 + \mu, \theta_{m+1} + \mu]$.
* `Subproblem.beta_le_opNorm`, `Subproblem.rightmost_compressionL_le`: $\beta_m \le \|H\|$, and the
  greatest Ritz value is at most $\lambda_{\max}(H)$.
* `Subproblem.residual_eq_zero_of_grade_le`: the restricted solution is exact at the grade.

## Proof outline

The proof follows the book. In Lanczos coordinates the residual is $\beta_{k-1} |\bar y_{k-1}|$ with
$\bar y = -\|g\| (T_k + \lambda_k)^{-1} e_0$, by (B.10.1)–(B.10.2). The $(k-1, 0)$ entry of the
inverse of a positive definite tridiagonal matrix decays geometrically (Lemma B.10.1,
`Matrix.abs_inv_apply_le_of_hasBandwidth_of_mem_Icc`). Moreover
$\|g\| \le (\theta_k + \lambda_k) \|s_k\|$ by (B.10.3), and $\beta_{k-1} \le \|H\|$ by (B.10.4).

## Implementation notes

* $\|H\|$ is the operator norm of $E$. For matrix data with a scaling $M$, the space $E$ carries the
  $M$-inner product (see `Numlib.Optimization.Subproblem.Matrix`), and $\|H\|$ is the largest
  $|\lambda|$ of the pencil $(H, M)$, that is, $\|M^{-1/2} H M^{-1/2}\|_2$. It is at most
  $\|M^{-1} H\|_2$ and can be smaller, because a similarity preserves the eigenvalues but not the
  Euclidean norm. The results are stated with $\|H\|$.
* In the iteration counts $\lceil \log A / \log((\sqrt{\kappa_*} + 1)/(\sqrt{\kappa_*} - 1))
  \rceil + 1$, the ceiling is `Nat.ceil`, so the bound is $k \le 1$ when $\log A < 0$. The case
  $\kappa_* = 1$, where $\log((\sqrt{\kappa_*} + 1)/(\sqrt{\kappa_*} - 1))$ is undefined, is stated
  separately: then $q_* = 0$, and the test holds at some $k \le \min(2, \operatorname{grade})$.
* The constant $\kappa_*$ can be any upper bound of the numbers $\kappa_k$ for
  $1 \le k \le \operatorname{grade}(H, g)$, such as their maximum (10.2.10).
-/

open Set Matrix Krylov
open scoped RealInnerProductSpace

namespace Subproblem

/-! ### The convergence factor -/

/-- The **convergence factor** $q(\kappa) = (\sqrt{\kappa} - 1) / (\sqrt{\kappa} + 1)$ of a
condition number $\kappa$. This is (10.2.9) of [cartis2022evaluation]. -/
noncomputable def convFactor (κ : ℝ) : ℝ := (√κ - 1) / (√κ + 1)

/-- The defining formula $q(\kappa) = (\sqrt{\kappa} - 1) / (\sqrt{\kappa} + 1)$. -/
theorem convFactor_def (κ : ℝ) : convFactor κ = (√κ - 1) / (√κ + 1) := rfl

/-- $q(\kappa) \ge 0$ for $\kappa \ge 1$. -/
theorem convFactor_nonneg {κ : ℝ} (hκ : 1 ≤ κ) : 0 ≤ convFactor κ := by
  have : 1 ≤ √κ := Real.one_le_sqrt.2 hκ
  unfold convFactor; positivity

/-- $q(\kappa) < 1$ for every real $\kappa$. -/
theorem convFactor_lt_one (κ : ℝ) : convFactor κ < 1 := by
  have : 0 ≤ √κ := Real.sqrt_nonneg κ
  rw [convFactor, div_lt_one (by positivity)]; linarith

/-- $q(\kappa) > 0$ for $\kappa > 1$. -/
theorem convFactor_pos {κ : ℝ} (hκ : 1 < κ) : 0 < convFactor κ := by
  have : 1 < √κ := Real.lt_sqrt_of_sq_lt (by simpa using hκ)
  unfold convFactor
  exact div_pos (by linarith) (by linarith)

/-- $q(1) = 0$: a perfectly conditioned system converges in one step. -/
@[simp]
theorem convFactor_one : convFactor 1 = 0 := by simp [convFactor]

/-- For $\kappa \ge 1$, $q(\kappa) = 0$ if and only if $\kappa = 1$. -/
theorem convFactor_eq_zero_iff {κ : ℝ} (hκ : 1 ≤ κ) : convFactor κ = 0 ↔ κ = 1 := by
  refine ⟨fun h => ?_, fun h => h ▸ convFactor_one⟩
  rcases hκ.eq_or_lt with h1 | h1
  · exact h1.symm
  · exact absurd h (convFactor_pos h1).ne'

/-- The convergence factor increases with the condition number: $\kappa \le \kappa'$ implies
$q(\kappa) \le q(\kappa')$. -/
theorem convFactor_le_convFactor {κ κ' : ℝ} (h : κ ≤ κ') :
    convFactor κ ≤ convFactor κ' := by
  have h1 : 0 ≤ √κ := Real.sqrt_nonneg κ
  have h2 : √κ ≤ √κ' := Real.sqrt_le_sqrt h
  rw [convFactor, convFactor, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **Iteration count for a geometric bound.** If $0 < q < 1$ and $A \in \mathbb{R}$, then
$A q^N \le 1$ for $N = \lceil \log A / \log(1/q) \rceil$, where the ceiling is `Nat.ceil`. -/
theorem mul_pow_le_one_of_ceil {A q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    A * q ^ ⌈Real.log A / Real.log (1 / q)⌉₊ ≤ 1 := by
  set N := ⌈Real.log A / Real.log (1 / q)⌉₊
  rcases le_or_gt A 0 with hA | hA
  · exact (mul_nonpos_of_nonpos_of_nonneg hA (by positivity)).trans zero_le_one
  have hlq : 0 < Real.log (1 / q) :=
    Real.log_pos (by rw [one_div]; exact one_lt_inv₀ hq0 |>.2 hq1)
  have hN : Real.log A ≤ N * Real.log (1 / q) := by
    rw [← div_le_iff₀ hlq]; exact Nat.le_ceil _
  have hqN : 0 < q ^ N := pow_pos hq0 N
  rw [← Real.log_pow, _root_.one_div_pow] at hN
  have := (Real.log_le_log_iff hA (by positivity)).1 hN
  rw [le_div_iff₀ hqN] at this
  linarith

/-- **From a geometric test to an iteration count.** Let $G \ge 1$ be a natural number and $A, q$
real numbers. Let $P$ be a property of natural numbers that holds at every $k \in [1, G]$ with
$A q^{k-1} \le 1$, and that holds at $k = G$. Then:

* if $0 < q < 1$, then $P(k)$ holds for some $k$ with $1 \le k \le \min(\lceil \log A /
  \log(1/q) \rceil + 1, G)$;
* if $q = 0$, then $P(k)$ holds for some $k$ with $1 \le k \le \min(2, G)$.

The ceiling is `Nat.ceil`. -/
theorem exists_le_min_of_geometric {P : ℕ → Prop} {G : ℕ} (hG : 1 ≤ G) {A q : ℝ}
    (hP : ∀ k, 1 ≤ k → k ≤ G → A * q ^ (k - 1) ≤ 1 → P k) (hPG : P G) :
    (0 < q → q < 1 →
      ∃ k, 1 ≤ k ∧ k ≤ min (⌈Real.log A / Real.log (1 / q)⌉₊ + 1) G ∧ P k) ∧
    (q = 0 → ∃ k, 1 ≤ k ∧ k ≤ min 2 G ∧ P k) := by
  constructor
  · intro hq0 hq1
    set N := ⌈Real.log A / Real.log (1 / q)⌉₊
    rcases le_total G (N + 1) with hle | hle
    · exact ⟨G, hG, le_min hle le_rfl, hPG⟩
    · refine ⟨N + 1, by omega, le_min le_rfl hle, hP _ (by omega) hle ?_⟩
      rw [Nat.add_sub_cancel]
      exact mul_pow_le_one_of_ceil hq0 hq1
  · rintro rfl
    rcases le_total G 2 with hle | hle
    · exact ⟨G, hG, le_min hle le_rfl, hPG⟩
    · exact ⟨2, by omega, le_min le_rfl hle, hP 2 (by omega) hle (by simp)⟩

/-! ### The shifted Lanczos tridiagonal -/

section Tridiagonal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : E →L[ℝ] E} {g : E}

/-- $\mathcal{K}_k$ denotes the Krylov subspace $\mathcal{K}_k(H, g)$ of the operator $H$ and the
gradient $g$. -/
local notation "𝒦ₕ[" k "]" => 𝒦[(H : E →ₗ[ℝ] E), g] k

/-- $q_j$ denotes the Lanczos vector `Arnoldi.vec H g j`. -/
local notation "𝐪" => Arnoldi.vec (H : E →ₗ[ℝ] E) g

/-- $T_m$ denotes the Lanczos tridiagonal matrix `Lanczos.tridiag H g m`. -/
local notation "𝐓" => Lanczos.tridiag (H : E →ₗ[ℝ] E) g

/-- $\beta_j$ denotes the Lanczos off-diagonal coefficient `Lanczos.beta H g j`. -/
local notation "𝛃" => Lanczos.beta (H : E →ₗ[ℝ] E) g

/-- The **condition number**
$$\kappa_k(\mu) = \frac{\theta_k + \mu}{\theta_1 + \mu}$$
of the shifted compression of $H$ to the Krylov subspace $\mathcal{K}_k(H, g)$, where
$\theta_1 \le \theta_k$ are the extreme eigenvalues of the compression (the extreme Ritz
values). At the multiplier $\mu = \lambda_k$ and for $k \le \operatorname{grade}(H, g)$, this is
the book's $\kappa_k = \kappa(T_k + \lambda_k I)$ of (10.2.8) in [cartis2022evaluation], by
`Subproblem.krylovCond_eq_ritzValues`.

The extreme eigenvalues are `Subproblem.leftmost` and `Subproblem.rightmost` of the compression.
If $\theta_1 + \mu = 0$, division by zero gives the value $0$. -/
noncomputable def krylovCond (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (g : E) (k : ℕ) (μ : ℝ) : ℝ :=
  (rightmost (isSymmetric_compressionL (K := 𝒦[(H : E →ₗ[ℝ] E), g] k) hH) + μ) /
    (leftmost (isSymmetric_compressionL (K := 𝒦[(H : E →ₗ[ℝ] E), g] k) hH) + μ)

omit [FiniteDimensional ℝ E] in
/-- Changing the witness for the dimension only reindexes the eigenvalues, so the set of eigenvalues
is the same. -/
private theorem range_eigenvalues_eq {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] {T : F →ₗ[ℝ] F} (hT : T.IsSymmetric) {n : ℕ}
    (hn : Module.finrank ℝ F = n) : range (hT.eigenvalues hn) = range (hT.eigenvalues rfl) := by
  subst hn; rfl

/-- **The extreme Ritz values are the extreme eigenvalues of the Lanczos tridiagonal matrix.** Let
$H$ be symmetric and $k \le \operatorname{grade}(H, g)$. Then the least and the greatest
eigenvalues $\theta_1$ and $\theta_k$ of the compression of $H$ to $\mathcal{K}_k$ are the least
and the greatest eigenvalues of $T_k$, that is, the infimum and the supremum of
`Lanczos.ritzValues`, the sorted eigenvalues of $T_k$.

Therefore `Subproblem.krylovCond` at $\lambda_k$ is the book's $\kappa(T_k + \lambda_k I) =
(\theta_{k,k} + \lambda_k) / (\theta_{1,k} + \lambda_k)$ of (10.2.8). -/
theorem leftmost_rightmost_compressionL_eq_ritzValues (hH : (H : E →ₗ[ℝ] E).IsSymmetric) {k : ℕ}
    (hk : k ≤ Krylov.grade (H : E →ₗ[ℝ] E) g) :
    leftmost (isSymmetric_compressionL (K := 𝒦ₕ[k]) hH) =
        ⨅ i, Lanczos.ritzValues (H : E →ₗ[ℝ] E) g k i ∧
      rightmost (isSymmetric_compressionL (K := 𝒦ₕ[k]) hH) =
        ⨆ i, Lanczos.ritzValues (H : E →ₗ[ℝ] E) g k i := by
  have hm : Module.finrank ℝ 𝒦ₕ[k] = k := by
    rw [Krylov.finrank_subspace, min_eq_left hk]
  have hr := Lanczos.ritzValues_eq_eigenvalues_compression g hH hm
  have hrange : range (Lanczos.ritzValues (H : E →ₗ[ℝ] E) g k) =
      range ((isSymmetric_compressionL (K := 𝒦ₕ[k]) hH).eigenvalues rfl) := by
    rw [hr]; exact range_eigenvalues_eq _ hm
  refine ⟨?_, ?_⟩
  · change sInf (range _) = sInf (range _); rw [hrange]
  · change sSup (range _) = sSup (range _); rw [hrange]

/-- The condition number in terms of the Ritz values: for $H$ symmetric and
$k \le \operatorname{grade}(H, g)$,
$$\kappa_k(\mu) = \frac{\lambda_{\max}(T_k) + \mu}{\lambda_{\min}(T_k) + \mu},$$
as in (10.2.8) of [cartis2022evaluation]. -/
theorem krylovCond_eq_ritzValues (hH : (H : E →ₗ[ℝ] E).IsSymmetric) {k : ℕ}
    (hk : k ≤ Krylov.grade (H : E →ₗ[ℝ] E) g) (μ : ℝ) :
    krylovCond hH g k μ = ((⨆ i, Lanczos.ritzValues (H : E →ₗ[ℝ] E) g k i) + μ) /
      ((⨅ i, Lanczos.ritzValues (H : E →ₗ[ℝ] E) g k i) + μ) := by
  obtain ⟨h1, h2⟩ := leftmost_rightmost_compressionL_eq_ritzValues hH hk
  rw [krylovCond, h1, h2]

/-- If $\mu > -\theta_1$, so that the shifted compression is positive definite, then
$\kappa_k(\mu) \ge 1$. -/
theorem one_le_krylovCond (hH : (H : E →ₗ[ℝ] E).IsSymmetric) {k : ℕ} {μ : ℝ}
    (hμ : -leftmost (isSymmetric_compressionL (K := 𝒦ₕ[k]) hH) < μ) :
    1 ≤ krylovCond hH g k μ := by
  rw [krylovCond, one_le_div (by linarith)]
  linarith [leftmost_le_rightmost (hH := isSymmetric_compressionL (K := 𝒦ₕ[k]) hH)]

/-- The quadratic form of the shifted compression to a subspace $K$ is that of $H$: $\langle (P_K
H|_K + \mu) v, v \rangle = \langle v, H v + \mu v \rangle$ for $v \in K$. -/
theorem inner_compressionL_add_smul_apply (K : Submodule ℝ E) (μ : ℝ) (v : K) :
    ⟪(compressionL H K + μ • (1 : K →L[ℝ] K)) v, v⟫ = ⟪(v : E), H v + μ • (v : E)⟫ := by
  simp only [_root_.add_apply, _root_.smul_apply, one_apply_eq_self, inner_add_left,
    inner_smul_left, inner_compressionL_left, inner_add_right, inner_smul_right, conj_trivial]
  rw [Submodule.coe_inner, real_inner_comm (H v)]

/-- **The extreme Ritz values enclose the quadratic form of the shifted Lanczos tridiagonal
matrix.** Let $H$ be symmetric, $g \neq 0$, $m + 1 \le \operatorname{grade}(H, g)$,
$T = T_{m+1}$, and let $\theta_1 \le \theta_{m+1}$ be the extreme eigenvalues of the compression
of $H$ to $\mathcal{K}_{m+1}$. Then for every $\mu$ and $x \in \mathbb{R}^{m+1}$,
$$(\theta_1 + \mu) \, x \cdot x \le x \cdot (T + \mu) x \le (\theta_{m+1} + \mu) \, x \cdot x.$$
-/
theorem dotProduct_tridiag_add_mem (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (hg : g ≠ 0) {m : ℕ}
    (hm : m + 1 ≤ Krylov.grade (H : E →ₗ[ℝ] E) g) (μ : ℝ) (x : Fin (m + 1) → ℝ) :
    (leftmost (isSymmetric_compressionL (K := 𝒦ₕ[m + 1]) hH) + μ) * (x ⬝ᵥ x) ≤
        x ⬝ᵥ ((𝐓 (m + 1) + μ • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) *ᵥ x) ∧
      x ⬝ᵥ ((𝐓 (m + 1) + μ • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) *ᵥ x) ≤
        (rightmost (isSymmetric_compressionL (K := 𝒦ₕ[m + 1]) hH) + μ) * (x ⬝ᵥ x) := by
  obtain ⟨-, hiso, hquad, -⟩ := krylov_lanczos_coordinates hH hg hm x x μ
  have hv : ∑ i, x i • 𝐪 i ∈ 𝒦ₕ[m + 1] :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Arnoldi.vec_mem_subspace_of_lt _ _ i.2)
  set v : 𝒦ₕ[m + 1] := ⟨_, hv⟩
  have hq : x ⬝ᵥ ((𝐓 (m + 1) + μ • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) *ᵥ x) =
      ⟪(compressionL H 𝒦ₕ[m + 1] + μ • (1 : 𝒦ₕ[m + 1] →L[ℝ] 𝒦ₕ[m + 1])) v, v⟫ := by
    rw [inner_compressionL_add_smul_apply, ← hquad]
  have hn : x ⬝ᵥ x = ‖v‖ ^ 2 := by
    rw [← hiso, ← real_inner_self_eq_norm_sq]; rfl
  rw [hq, hn]
  constructor
  · rw [add_comm (leftmost _)]; exact add_leftmost_mul_norm_sq_le μ v
  · rw [add_comm (rightmost _)]; exact inner_add_smul_le_add_rightmost μ v

/-- **The shifted Lanczos tridiagonal matrix is positive definite** when the shift lies to the right
of the least Ritz value. Let $H$ be symmetric, $g \neq 0$ and
$m + 1 \le \operatorname{grade}(H, g)$. If $\mu > -\theta_1$, then $T_{m+1} + \mu$ is positive
definite. -/
theorem posDef_tridiag_add (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (hg : g ≠ 0) {m : ℕ}
    (hm : m + 1 ≤ Krylov.grade (H : E →ₗ[ℝ] E) g) {μ : ℝ}
    (hμ : -leftmost (isSymmetric_compressionL (K := 𝒦ₕ[m + 1]) hH) < μ) :
    (𝐓 (m + 1) + μ • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · exact Matrix.isHermitian_iff_isSymm.2
      ((Lanczos.tridiag_isSymm _ _ _).add (Matrix.isSymm_one.smul μ))
  · have hxx : 0 < x ⬝ᵥ x := by
      rcases Function.ne_iff.1 hx with ⟨i, hi⟩
      exact lt_of_lt_of_le (mul_self_pos.2 hi)
        (Finset.single_le_sum (f := fun j => x j * x j) (fun j _ => mul_self_nonneg (x j))
          (Finset.mem_univ i))
    have := (dotProduct_tridiag_add_mem hH hg hm μ x).1
    simp only [star_trivial]
    nlinarith

/-- Let $H$ be symmetric, $g \neq 0$ and $m + 1 \le \operatorname{grade}(H, g)$, and let
$T_{m+1} + \mu$ be positive definite. Then every eigenvalue of $T_{m+1} + \mu$ lies in
$[\theta_1 + \mu, \theta_{m+1} + \mu]$. -/
theorem eigenvalues_tridiag_add_mem (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (hg : g ≠ 0) {m : ℕ}
    (hm : m + 1 ≤ Krylov.grade (H : E →ₗ[ℝ] E) g) {μ : ℝ}
    (hG : (𝐓 (m + 1) + μ • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)).PosDef)
    (i : Fin (m + 1)) :
    hG.1.eigenvalues i ∈ Icc (leftmost (isSymmetric_compressionL (K := 𝒦ₕ[m + 1]) hH) + μ)
      (rightmost (isSymmetric_compressionL (K := 𝒦ₕ[m + 1]) hH) + μ) := by
  set v := hG.1.eigenvectorBasis i
  have hvv : ⇑v ⬝ᵥ ⇑v = 1 := by
    have h := EuclideanSpace.inner_eq_star_dotProduct v v
    rw [real_inner_self_eq_norm_sq, hG.1.eigenvectorBasis.norm_eq_one, one_pow] at h
    simpa using h.symm
  have he := hG.1.eigenvalues_eq i
  simp only [star_trivial, RCLike.re_to_real] at he
  obtain ⟨h1, h2⟩ := dotProduct_tridiag_add_mem hH hg hm μ ⇑v
  rw [hvv, mul_one] at h1 h2
  exact ⟨he ▸ h1, he ▸ h2⟩

omit [FiniteDimensional ℝ E] in
/-- The shifted Lanczos matrix $T_m + \mu$ is tridiagonal. -/
theorem tridiag_add_isTridiagonal (m : ℕ) (μ : ℝ) :
    (𝐓 m + μ • (1 : Matrix (Fin m) (Fin m) ℝ)).IsTridiagonal := by
  intro i j hij
  have hne : i ≠ j := by
    rintro rfl
    rcases hij with ⟨k, h1, h2⟩ | ⟨k, h1, h2⟩ <;> exact absurd (h1.trans h2) (lt_irrefl _)
  rw [Matrix.add_apply, Lanczos.tridiag_isTridiagonal _ _ _ i j hij, Matrix.smul_apply,
    Matrix.one_apply_ne hne, smul_zero, add_zero]

omit [FiniteDimensional ℝ E] in
/-- The Lanczos off-diagonal coefficients are bounded by the operator norm: $\beta_m \le \|H\|$ for
every $m$.

This is the correct form of (B.10.4) of [cartis2022evaluation], which the book states as
$\gamma_{k+1} \le \|M^{-1} H\|$. -/
theorem beta_le_opNorm (m : ℕ) : 𝛃 m ≤ ‖H‖ := by
  rw [Lanczos.beta, Arnoldi.w_eq_sub_starProjection, ← Submodule.starProjection_orthogonal_val]
  refine (Submodule.norm_starProjection_apply_le _ _).trans ?_
  rw [ContinuousLinearMap.coe_coe]
  refine (H.le_opNorm _).trans ?_
  rcases eq_or_ne (𝐪 m) 0 with h | h
  · rw [h, norm_zero, mul_zero]; exact norm_nonneg _
  · rw [Arnoldi.norm_vec_eq_one_of_ne_zero _ _ h, mul_one]

end Tridiagonal

/-! ### The residual bound -/

section Residual

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : E →L[ℝ] E} {g : E}

/-- $\mathcal{K}_k$ denotes the Krylov subspace $\mathcal{K}_k(H, g)$ of the operator $H$ and the
gradient $g$. -/
local notation "𝒦ₕ[" k "]" => 𝒦[(H : E →ₗ[ℝ] E), g] k

/-- $q_j$ denotes the Lanczos vector `Arnoldi.vec H g j`. -/
local notation "𝐪" => Arnoldi.vec (H : E →ₗ[ℝ] E) g

/-- $T_m$ denotes the Lanczos tridiagonal matrix `Lanczos.tridiag H g m`. -/
local notation "𝐓" => Lanczos.tridiag (H : E →ₗ[ℝ] E) g

/-- $\beta_j$ denotes the Lanczos off-diagonal coefficient `Lanczos.beta H g j`. -/
local notation "𝛃" => Lanczos.beta (H : E →ₗ[ℝ] E) g

/-- **Exactness at the grade.** Let $k \ge 1$ and $\operatorname{grade}(H, g) \le k$, so that
$\mathcal{K}_k$ is the whole Krylov space and is $H$-invariant. If $s \in \mathcal{K}_k$ and the
residual $g + H s + \mu s$ is orthogonal to $\mathcal{K}_k$, then $g + H s + \mu s = 0$. -/
theorem residual_eq_zero_of_grade_le {k : ℕ} (hk : 1 ≤ k)
    (hgr : Krylov.grade (H : E →ₗ[ℝ] E) g ≤ k) {s : E} {μ : ℝ} (hs : s ∈ 𝒦ₕ[k])
    (hgal : ∀ v ∈ 𝒦ₕ[k], ⟪g + H s + μ • s, v⟫ = 0) : g + H s + μ • s = 0 := by
  have hinv : 𝒦ₕ[k] ∈ Module.End.invtSubmodule (H : E →ₗ[ℝ] E) := by
    rw [Krylov.subspace_eq_of_grade_le _ _ hgr]
    exact Krylov.subspace_grade_mem_invtSubmodule _ _
  have hHs : H s ∈ 𝒦ₕ[k] :=
    (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).1 hinv s hs
  have hr : g + H s + μ • s ∈ 𝒦ₕ[k] :=
    Submodule.add_mem _ (Submodule.add_mem _ (mem_krylov H g hk) hHs) (Submodule.smul_mem _ _ hs)
  exact inner_self_eq_zero.1 (hgal _ hr)

/-- **The restricted first-order condition in Lanczos coordinates.** Let $H$ be symmetric,
$g \neq 0$ and $m + 1 \le \operatorname{grade}(H, g)$. Let $s \in \mathcal{K}_{m+1}$ be such
that $g + H s + \mu s$ is orthogonal to $\mathcal{K}_{m+1}$, and let
$\bar y_j = \langle q_j, s \rangle$ be its Lanczos coordinates. Then
$$(T_{m+1} + \mu) \bar y = -\|g\| e_0 \quad \text{and} \quad \|g + H s + \mu s\| = \beta_m |\bar
  y_m|.$$
This is (10.2.2) and (B.10.1) of [cartis2022evaluation]. -/
theorem lanczos_galerkin (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (hg : g ≠ 0) {m : ℕ}
    (hm : m + 1 ≤ Krylov.grade (H : E →ₗ[ℝ] E) g) {s : E} {μ : ℝ} (hs : s ∈ 𝒦ₕ[m + 1])
    (hgal : ∀ v ∈ 𝒦ₕ[m + 1], ⟪g + H s + μ • s, v⟫ = 0) :
    (𝐓 (m + 1) + μ • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) *ᵥ (fun j => ⟪𝐪 j, s⟫) =
        -(Pi.single 0 ‖g‖ : Fin (m + 1) → ℝ) ∧
      ‖g + H s + μ • s‖ = 𝛃 m * |⟪𝐪 m, s⟫| := by
  set y : Fin (m + 1) → ℝ := fun j => ⟪𝐪 j, s⟫
  have hsy : ∑ j, y j • 𝐪 j = s := (eq_sum_inner_vec hs).symm
  obtain ⟨hrel, -, -, hnorm⟩ := krylov_lanczos_coordinates hH hg hm y y μ
  rw [hsy] at hrel hnorm
  have hsys : (𝐓 (m + 1) + μ • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) *ᵥ y =
      -(Pi.single 0 ‖g‖ : Fin (m + 1) → ℝ) := by
    rw [eq_neg_iff_add_eq_zero]
    funext i
    have h0 := hgal _ (Arnoldi.vec_mem_subspace_of_lt _ _ i.2)
    rw [hrel, real_inner_comm, inner_add_right, inner_vec_sum hm, real_inner_smul_right,
      Arnoldi.inner_vec_eq_zero _ _ (by have := i.2; omega), mul_zero, add_zero] at h0
    exact h0
  refine ⟨hsys, ?_⟩
  rw [hnorm hsys]
  simp [y]

/-- **The size of a restricted solution.** Let $H$ be symmetric and $k \ge 1$. If
$s \in \mathcal{K}_k$ satisfies the condition that $g + H s + \mu s$ is orthogonal to
$\mathcal{K}_k$, with $\mu \ge -\theta_1$, then
$$\|g\| \le (\theta_k + \mu) \|s\|,$$
where $\theta_k$ is the greatest Ritz value. This is used in the proofs of Theorem 10.2.2 and
Corollary 10.2.3 of [cartis2022evaluation]. -/
theorem norm_le_of_galerkin_krylov (hH : (H : E →ₗ[ℝ] E).IsSymmetric) {k : ℕ} (hk : 1 ≤ k)
    {s : E} {μ : ℝ} (hs : s ∈ 𝒦ₕ[k]) (hgal : ∀ v ∈ 𝒦ₕ[k], ⟪g + H s + μ • s, v⟫ = 0)
    (hμ : -leftmost (isSymmetric_compressionL (K := 𝒦ₕ[k]) hH) ≤ μ) :
    ‖g‖ ≤ (rightmost (isSymmetric_compressionL (K := 𝒦ₕ[k]) hH) + μ) * ‖s‖ := by
  have hsh := (compressionL_shifted_iff hs).2 hgal
  have h := norm_add_smul_apply_le (hH := isSymmetric_compressionL (K := 𝒦ₕ[k]) hH) hμ ⟨s, hs⟩
  rw [hsh, norm_neg, orthogonalProjectionOnto_krylov hk] at h
  simp only [add_comm μ] at h
  exact h

/-- **The residual bound.** Let $H$ be symmetric, $g \neq 0$ and $k \ge 1$. Let
$s \in \mathcal{K}_k$ be such that $g + H s + \mu s$ is orthogonal to $\mathcal{K}_k$, and let
the shift satisfy $\mu > -\theta_1$, where $\theta_1$ is the least Ritz value of
$\mathcal{K}_k$; then $\kappa = \kappa_k(\mu)$ is the condition number of the positive definite
matrix $T_k + \mu$. Then
$$\|g + H s + \mu s\| \le 2 \|H\| \, \kappa \, \|s\| \, q(\kappa)^{k-1}, \qquad q(\kappa) =
  \frac{\sqrt{\kappa} - 1}{\sqrt{\kappa} + 1}.$$
This is the core of Theorems 10.2.2 and 10.3.2 of [cartis2022evaluation], which follow Gould and
Simoncini.

In Lanczos coordinates the residual is $\beta_{k-1} |\bar y_{k-1}|$ with
$\bar y = -\|g\| (T_k + \mu)^{-1} e_0$. The $(k-1, 0)$ entry of the inverse of the positive
definite tridiagonal matrix $T_k + \mu$ is at most $2 q^{k-1} / (\theta_1 + \mu)$ (Lemma B.10.1,
`Matrix.abs_inv_apply_le_of_hasBandwidth_of_mem_Icc`); moreover $\|g\| = \|(PH| + \mu) s\| \le
(\theta_k + \mu) \|s\|$ and $\beta_{k-1} \le \|H\|$. Beyond the grade the residual is $0$. -/
theorem krylov_residual_le (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (hg : g ≠ 0) {k : ℕ} (hk : 1 ≤ k)
    {s : E} {μ : ℝ} (hs : s ∈ 𝒦ₕ[k]) (hgal : ∀ v ∈ 𝒦ₕ[k], ⟪g + H s + μ • s, v⟫ = 0)
    (hμ : -leftmost (isSymmetric_compressionL (K := 𝒦ₕ[k]) hH) < μ) :
    ‖g + H s + μ • s‖ ≤
      2 * ‖H‖ * krylovCond hH g k μ * ‖s‖ * convFactor (krylovCond hH g k μ) ^ (k - 1) := by
  have hκ := one_le_krylovCond (g := g) hH hμ
  rcases le_or_gt (Krylov.grade (H : E →ₗ[ℝ] E) g) k with hgr | hgr
  · rw [residual_eq_zero_of_grade_le hk hgr hs hgal, norm_zero]
    have := convFactor_nonneg hκ
    positivity
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hm : m + 1 ≤ Krylov.grade (H : E →ₗ[ℝ] E) g := hgr.le
  set hC := isSymmetric_compressionL (K := 𝒦ₕ[m + 1]) hH
  set a := leftmost hC + μ
  set b := rightmost hC + μ
  have ha : 0 < a := by simp only [a]; linarith
  have hab : a ≤ b := by simp only [a, b]; linarith [leftmost_le_rightmost (hH := hC)]
  have hcond : krylovCond hH g (m + 1) μ = b / a := rfl
  obtain ⟨hsys, hres⟩ := lanczos_galerkin hH hg hm hs hgal
  set y : Fin (m + 1) → ℝ := fun j => ⟪𝐪 j, s⟫
  set G := 𝐓 (m + 1) + μ • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
  have hG : G.PosDef := posDef_tridiag_add hH hg hm hμ
  -- the last Lanczos coordinate through the inverse
  have hy : y = G⁻¹ *ᵥ (-(Pi.single 0 ‖g‖ : Fin (m + 1) → ℝ)) := by
    rw [← hsys, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det G).1 hG.isUnit), Matrix.one_mulVec]
  have hylast : |⟪𝐪 m, s⟫| = ‖g‖ * |G⁻¹ (Fin.last m) 0| := by
    have h := congrFun hy (Fin.last m)
    simp only [y, Fin.val_last] at h
    rw [h, Matrix.mulVec_neg]
    simp [abs_mul]
  -- the decay of the inverse
  obtain ⟨hl, hu⟩ := isTridiagonal_iff_hasBandwidth_one.1
    (tridiag_add_isTridiagonal (H := H) (g := g) (m + 1) μ)
  have hdecay := abs_inv_apply_le_of_hasBandwidth_of_mem_Icc hG hl hu ha
    (eigenvalues_tridiag_add_mem hH hg hm hG) (Fin.last m) 0
  simp only [Fin.val_last, Fin.val_zero, Nat.cast_zero, sub_zero, Int.natAbs_natCast,
    Nat.cast_one, div_one, Nat.ceil_natCast] at hdecay
  have hgs : ‖g‖ ≤ b * ‖s‖ := norm_le_of_galerkin_krylov hH (by omega) hs hgal hμ.le
  have hβ := beta_le_opNorm (H := H) (g := g) m
  have hq := convFactor_nonneg (one_le_krylovCond (g := g) hH hμ)
  rw [hcond] at hq ⊢
  rw [hres, hylast, Nat.add_sub_cancel]
  have hβ0 := Lanczos.beta_nonneg (H : E →ₗ[ℝ] E) g m
  calc 𝛃 m * (‖g‖ * |G⁻¹ (Fin.last m) 0|)
      ≤ ‖H‖ * ((b * ‖s‖) * (2 / a * convFactor (b / a) ^ m)) := by
        refine mul_le_mul hβ (mul_le_mul hgs hdecay (abs_nonneg _)
          (mul_nonneg (by linarith) (norm_nonneg _))) (by positivity) (norm_nonneg _)
    _ = 2 * ‖H‖ * (b / a) * ‖s‖ * convFactor (b / a) ^ m := by
        field_simp

/-- **Interlacing at the top.** Let $H$ be symmetric and let $K$ be a nonzero subspace. Then the
greatest eigenvalue of the compression $P_K H|_K$ is at most the greatest eigenvalue
$\lambda_{\max}$ of $H$. This is used in the proof of Corollary 10.2.3 of
[cartis2022evaluation]. -/
theorem rightmost_compressionL_le (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (K : Submodule ℝ E)
    [Nontrivial K] : rightmost (isSymmetric_compressionL (K := K) hH) ≤ rightmost hH :=
  rightmost_le_of_forall fun v => by
    rw [inner_compressionL_right]
    exact inner_le_rightmost_mul_norm_sq (hH := hH) (v : E)

/-- **Bound on the gradient at the Krylov subspace minimizer of the regularized model.** Let $H$ be
symmetric, $g \neq 0$, $\sigma > 0$, $r > 2$ and $k \ge 1$. Let $s_k \in \mathcal{K}_k(H, g)$
minimize the regularized model over $\mathcal{K}_k(H, g)$, with multiplier
$\lambda_k = \sigma \|s_k\|^{r-2}$ as in (10.2.3), and let $\kappa_k = \kappa_k(\lambda_k)$ as
in (10.2.8). Then the gradient of the regularized model satisfies
$$\|g + H s_k + \lambda_k s_k\| \le 2 \|H\| \, \kappa_k
  \left(\frac{\lambda_k}{\sigma}\right)^{1/(r-2)} \left(\frac{\sqrt{\kappa_k} -
  1}{\sqrt{\kappa_k} + 1}\right)^{k-1}.$$
This is Theorem 10.2.2 of [cartis2022evaluation], (10.2.9), which follows Gould and Simoncini.

Here $\|H\|$ is the operator norm of $E$. For scaled data it is the largest $|\lambda|$ of the
pencil $(H, M)$, which is at most the book's $\|M^{-1} H\|$. -/
theorem krylov_gradient_bound_regularization (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (hg : g ≠ 0)
    {σ r : ℝ} (hσ : 0 < σ) (hr : 2 < r) {k : ℕ} (hk : 1 ≤ k) {s : E} (hs : s ∈ 𝒦ₕ[k])
    (hmin : IsMinOn (regModel g H σ r) (𝒦ₕ[k] : Set E) s) :
    ‖g + H s + (σ * ‖s‖ ^ (r - 2)) • s‖ ≤
      2 * ‖H‖ * krylovCond hH g k (σ * ‖s‖ ^ (r - 2)) *
        (σ * ‖s‖ ^ (r - 2) / σ) ^ (1 / (r - 2)) *
        convFactor (krylovCond hH g k (σ * ‖s‖ ^ (r - 2))) ^ (k - 1) := by
  have hn : (σ * ‖s‖ ^ (r - 2) / σ) ^ (1 / (r - 2)) = ‖s‖ := by
    rw [mul_div_cancel_left₀ _ hσ.ne', one_div,
      Real.rpow_rpow_inv (norm_nonneg _) (by linarith : r - 2 ≠ 0)]
  rw [hn]
  exact krylov_residual_le hH hg hk hs (galerkin_of_isMinOn_regModel_subspace hH hσ hr hs hmin).1
    (neg_leftmost_lt_of_isMinOn_regModel_krylov hH hg hσ hr hk hs hmin).1

/-- **Bound on the residual at the Krylov subspace trust-region solution.** Let $H$ be symmetric,
$g \neq 0$ and $k \ge 1$. Let $s_k \in \mathcal{K}_k$ satisfy $\|s_k\| \le \Delta$ and have the
trust-region multiplier $\lambda_k$ (`Subproblem.IsTrustRegionMultiplier`) for the subproblem
restricted to $\mathcal{K}_k$, that is, for the compressed data. Let
$\kappa_k = \kappa_k(\lambda_k)$. Then the residual (10.3.1) satisfies
$$\|g + H s_k + \lambda_k s_k\| \le 2 \|H\| \, \kappa_k \, \Delta \left(\frac{\sqrt{\kappa_k} -
  1}{\sqrt{\kappa_k} + 1}\right)^{k-1}.$$
This is Theorem 10.3.2 of [cartis2022evaluation]. -/
theorem krylov_residual_bound_trustRegion (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (hg : g ≠ 0)
    {Δ μ : ℝ} {k : ℕ} (hk : 1 ≤ k) {s : E} (hs : s ∈ 𝒦ₕ[k]) (hsΔ : ‖s‖ ≤ Δ)
    (h : IsTrustRegionMultiplier ((𝒦ₕ[k]).orthogonalProjectionOnto g) (compressionL H _) Δ
      ⟨s, hs⟩ μ) :
    ‖g + H s + μ • s‖ ≤
      2 * ‖H‖ * krylovCond hH g k μ * Δ * convFactor (krylovCond hH g k μ) ^ (k - 1) := by
  have hμ := (neg_leftmost_lt_of_isTrustRegionMultiplier_krylov hH hg hk hs h).1
  refine (krylov_residual_le hH hg hk hs (h.galerkin_of_compressionL hs) hμ).trans ?_
  have hκ := one_le_krylovCond (g := g) hH hμ
  have hq := convFactor_nonneg hκ
  gcongr

/-- **Iteration bound for the Krylov approximation, regularization.** Let $H$ be symmetric,
$g \neq 0$, $\sigma > 0$, $r > 2$ and $\theta > 0$; here $\theta$ is the constant $\theta_1$ of
the stopping rule (9.3.14b). Let $(s_k)$ be a sequence with $s_k \in \mathcal{K}_k(H, g)$ for
all $k$, such that for $1 \le k \le \operatorname{grade}(H, g)$ the point $s_k$ minimizes the
regularized model over $\mathcal{K}_k(H, g)$, with multiplier
$\lambda_k = \sigma \|s_k\|^{r-2}$. Let $s_*$ be a global minimizer of the regularized model,
with $\lambda_* = \sigma \|s_*\|^{r-2}$, let $\lambda_{\max}$ be the greatest eigenvalue of $H$,
let $\kappa_*$ be an upper bound of the numbers $\kappa_k(\lambda_k)$ for
$1 \le k \le \operatorname{grade}(H, g)$, let $q_* = q(\kappa_*)$, and let
$$A = \frac{4 \|H\| \kappa_*}{\theta} \left(\frac{\lambda_*}{\sigma}\right)^{1/(r-2)}
  \left(\frac{\lambda_{\max} + \lambda_*}{\|g\|}\right)^2.$$
Then the stopping rule (9.3.14b), $\|g + H s_k + \lambda_k s_k\| \le \frac12 \theta \|s_k\|^2$,
holds:

* (i) at every $k \in [1, \operatorname{grade}]$ with $A q_*^{k-1} \le 1$;
* (ii) at $k = \operatorname{grade}$;
* (iii) if $\kappa_* > 1$, at some $k$ with $1 \le k \le \min(\lceil \log A / \log(1/q_*)
  \rceil + 1, \operatorname{grade})$;
* (iv) if $\kappa_* = 1$, at some $k$ with $1 \le k \le \min(2, \operatorname{grade})$.

This is Corollary 10.2.3 of [cartis2022evaluation].

The ceiling is `Nat.ceil`, since $\log A$ may be negative. The case $\kappa_* = 1$, where
$\log((\sqrt{\kappa_*} + 1)/(\sqrt{\kappa_*} - 1))$ is undefined, is stated separately. -/
theorem krylov_iteration_bound_regularization (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (hg : g ≠ 0)
    {σ r θ : ℝ} (hσ : 0 < σ) (hr : 2 < r) (hθ : 0 < θ) {s : ℕ → E}
    (hs : ∀ k, s k ∈ 𝒦ₕ[k])
    (hmin : ∀ k, 1 ≤ k → k ≤ Krylov.grade (H : E →ₗ[ℝ] E) g →
      IsMinOn (regModel g H σ r) (𝒦ₕ[k] : Set E) (s k))
    {sstar : E} (hstar : IsMinOn (regModel g H σ r) univ sstar) {κs : ℝ}
    (hκs : ∀ k, 1 ≤ k → k ≤ Krylov.grade (H : E →ₗ[ℝ] E) g →
      krylovCond hH g k (σ * ‖s k‖ ^ (r - 2)) ≤ κs) :
    (∀ k, 1 ≤ k → k ≤ Krylov.grade (H : E →ₗ[ℝ] E) g →
      4 * ‖H‖ * κs / θ * (σ * ‖sstar‖ ^ (r - 2) / σ) ^ (1 / (r - 2)) *
          ((rightmost hH + σ * ‖sstar‖ ^ (r - 2)) / ‖g‖) ^ 2 * convFactor κs ^ (k - 1) ≤ 1 →
        ‖g + H (s k) + (σ * ‖s k‖ ^ (r - 2)) • s k‖ ≤ 1 / 2 * θ * ‖s k‖ ^ 2) ∧
    ‖g + H (s (Krylov.grade (H : E →ₗ[ℝ] E) g)) +
        (σ * ‖s (Krylov.grade (H : E →ₗ[ℝ] E) g)‖ ^ (r - 2)) • s (Krylov.grade (H : E →ₗ[ℝ] E) g)‖ ≤
      1 / 2 * θ * ‖s (Krylov.grade (H : E →ₗ[ℝ] E) g)‖ ^ 2 ∧
    (1 < κs → ∃ k, 1 ≤ k ∧
      k ≤ min (⌈Real.log (4 * ‖H‖ * κs / θ * (σ * ‖sstar‖ ^ (r - 2) / σ) ^ (1 / (r - 2)) *
          ((rightmost hH + σ * ‖sstar‖ ^ (r - 2)) / ‖g‖) ^ 2) /
          Real.log (1 / convFactor κs)⌉₊ + 1) (Krylov.grade (H : E →ₗ[ℝ] E) g) ∧
      ‖g + H (s k) + (σ * ‖s k‖ ^ (r - 2)) • s k‖ ≤ 1 / 2 * θ * ‖s k‖ ^ 2) ∧
    (κs = 1 → ∃ k, 1 ≤ k ∧ k ≤ min 2 (Krylov.grade (H : E →ₗ[ℝ] E) g) ∧
      ‖g + H (s k) + (σ * ‖s k‖ ^ (r - 2)) • s k‖ ≤ 1 / 2 * θ * ‖s k‖ ^ 2) := by
  set G := Krylov.grade (H : E →ₗ[ℝ] E) g
  set lstar := σ * ‖sstar‖ ^ (r - 2)
  set A := 4 * ‖H‖ * κs / θ * (lstar / σ) ^ (1 / (r - 2)) * ((rightmost hH + lstar) / ‖g‖) ^ 2
  have hG : 1 ≤ G := Krylov.grade_pos_of_ne_zero _ _ hg
  have hgn : 0 < ‖g‖ := norm_pos_iff.2 hg
  have hsn : (lstar / σ) ^ (1 / (r - 2)) = ‖sstar‖ := by
    rw [mul_div_cancel_left₀ _ hσ.ne', one_div,
      Real.rpow_rpow_inv (norm_nonneg _) (by linarith : r - 2 ≠ 0)]
  -- the geometric test
  have hP : ∀ k, 1 ≤ k → k ≤ G → A * convFactor κs ^ (k - 1) ≤ 1 →
      ‖g + H (s k) + (σ * ‖s k‖ ^ (r - 2)) • s k‖ ≤ 1 / 2 * θ * ‖s k‖ ^ 2 := by
    intro k hk hkG hA
    have hgal := (galerkin_of_isMinOn_regModel_subspace hH hσ hr (hs k) (hmin k hk hkG)).1
    have hμ := (neg_leftmost_lt_of_isMinOn_regModel_krylov hH hg hσ hr hk (hs k)
      (hmin k hk hkG)).1
    have hκ := one_le_krylovCond (g := g) hH hμ
    have hκk := hκs k hk hkG
    obtain ⟨hlam, hnorm⟩ := regMultiplier_le_of_inner_eq_zero hH hσ hr (hs k) hgal hstar
    -- the upper bound on the gradient
    have hup : ‖g + H (s k) + (σ * ‖s k‖ ^ (r - 2)) • s k‖ ≤
        2 * ‖H‖ * κs * ‖sstar‖ * convFactor κs ^ (k - 1) := by
      refine (krylov_residual_le hH hg hk (hs k) hgal hμ).trans ?_
      have hq0 := convFactor_nonneg hκ
      have hq := convFactor_le_convFactor hκk
      have hκs0 : 0 ≤ κs := by linarith
      gcongr
    -- the lower bound on the step
    have : Nontrivial 𝒦ₕ[k] :=
      ⟨⟨⟨g, mem_krylov H g hk⟩, 0, fun h => hg (congrArg Subtype.val h)⟩⟩
    have hθk := rightmost_compressionL_le hH 𝒦ₕ[k]
    have hgs := norm_le_of_galerkin_krylov hH hk (hs k) hgal hμ.le
    have hlow : ‖g‖ ≤ (rightmost hH + lstar) * ‖s k‖ :=
      hgs.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
    have hD : 0 < rightmost hH + lstar := by
      by_contra hD
      push Not at hD
      have := mul_nonpos_of_nonpos_of_nonneg hD (norm_nonneg (s k))
      linarith
    have hsk : ‖g‖ / (rightmost hH + lstar) ≤ ‖s k‖ := by rwa [div_le_iff₀' hD]
    have hR : 2 * ‖H‖ * κs * ‖sstar‖ * convFactor κs ^ (k - 1) =
        1 / 2 * θ * (‖g‖ / (rightmost hH + lstar)) ^ 2 * (A * convFactor κs ^ (k - 1)) := by
      simp only [A, hsn]
      field_simp
      ring
    calc _ ≤ 2 * ‖H‖ * κs * ‖sstar‖ * convFactor κs ^ (k - 1) := hup
      _ = 1 / 2 * θ * (‖g‖ / (rightmost hH + lstar)) ^ 2 * (A * convFactor κs ^ (k - 1)) := hR
      _ ≤ 1 / 2 * θ * (‖g‖ / (rightmost hH + lstar)) ^ 2 * 1 := by gcongr
      _ ≤ 1 / 2 * θ * ‖s k‖ ^ 2 := by
        rw [mul_one]; gcongr
  -- exactness at the grade
  have hPG : ‖g + H (s G) + (σ * ‖s G‖ ^ (r - 2)) • s G‖ ≤ 1 / 2 * θ * ‖s G‖ ^ 2 := by
    rw [residual_eq_zero_of_grade_le hG le_rfl (hs G)
      (galerkin_of_isMinOn_regModel_subspace hH hσ hr (hs G) (hmin G hG le_rfl)).1, norm_zero]
    positivity
  obtain ⟨h1, h2⟩ := exists_le_min_of_geometric hG hP hPG
  refine ⟨hP, hPG, fun hκ => h1 (convFactor_pos hκ) (convFactor_lt_one κs), fun hκ => h2 ?_⟩
  rw [hκ, convFactor_one]

/-- **Iteration bound for the Krylov approximation, trust region.** Let $H$ be symmetric, $g \neq 0$
and $\varepsilon > 0$. Let $(s_k)$ be a sequence with $s_k \in \mathcal{K}_k$ for all $k$, such
that for $1 \le k \le \operatorname{grade}(H, g)$ we have $\|s_k\| \le \Delta$ and $s_k$ has the
trust-region multiplier $\lambda_k$ for the subproblem restricted to $\mathcal{K}_k$. Let
$\kappa_*$ be an upper bound of the numbers $\kappa_k(\lambda_k)$ for
$1 \le k \le \operatorname{grade}(H, g)$, and let $q_* = q(\kappa_*)$. Then the residual test
(10.3.2), $\|g + H s_k + \lambda_k s_k\| \le \varepsilon$, holds:

* (i) at every $k \in [1, \operatorname{grade}]$ with $2 \|H\| \kappa_* \Delta q_*^{k-1} \le
  \varepsilon$;
* (ii) at $k = \operatorname{grade}$;
* (iii) if $\kappa_* > 1$, at some $k$ with $1 \le k \le \min(\lceil \log(2 \|H\| \kappa_*
  \Delta / \varepsilon) / \log(1/q_*) \rceil + 1, \operatorname{grade})$;
* (iv) if $\kappa_* = 1$, at some $k$ with $1 \le k \le \min(2, \operatorname{grade})$.

This is Corollary 10.3.3 of [cartis2022evaluation]. The ceiling is `Nat.ceil`. -/
theorem krylov_iteration_bound_trustRegion (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (hg : g ≠ 0)
    {Δ ε : ℝ} (hε : 0 < ε) {s : ℕ → E} {μ : ℕ → ℝ} (hs : ∀ k, s k ∈ 𝒦ₕ[k])
    (hmul : ∀ k, 1 ≤ k → k ≤ Krylov.grade (H : E →ₗ[ℝ] E) g → ‖s k‖ ≤ Δ ∧
      IsTrustRegionMultiplier ((𝒦ₕ[k]).orthogonalProjectionOnto g) (compressionL H _) Δ
        ⟨s k, hs k⟩ (μ k))
    {κs : ℝ} (hκs : ∀ k, 1 ≤ k → k ≤ Krylov.grade (H : E →ₗ[ℝ] E) g →
      krylovCond hH g k (μ k) ≤ κs) :
    (∀ k, 1 ≤ k → k ≤ Krylov.grade (H : E →ₗ[ℝ] E) g →
      2 * ‖H‖ * κs * Δ * convFactor κs ^ (k - 1) ≤ ε → ‖g + H (s k) + μ k • s k‖ ≤ ε) ∧
    ‖g + H (s (Krylov.grade (H : E →ₗ[ℝ] E) g)) +
        μ (Krylov.grade (H : E →ₗ[ℝ] E) g) • s (Krylov.grade (H : E →ₗ[ℝ] E) g)‖ ≤ ε ∧
    (1 < κs → ∃ k, 1 ≤ k ∧
      k ≤ min (⌈Real.log (2 * ‖H‖ * κs * Δ / ε) / Real.log (1 / convFactor κs)⌉₊ + 1)
        (Krylov.grade (H : E →ₗ[ℝ] E) g) ∧ ‖g + H (s k) + μ k • s k‖ ≤ ε) ∧
    (κs = 1 → ∃ k, 1 ≤ k ∧ k ≤ min 2 (Krylov.grade (H : E →ₗ[ℝ] E) g) ∧
      ‖g + H (s k) + μ k • s k‖ ≤ ε) := by
  set G := Krylov.grade (H : E →ₗ[ℝ] E) g
  have hG : 1 ≤ G := Krylov.grade_pos_of_ne_zero _ _ hg
  have hP : ∀ k, 1 ≤ k → k ≤ G → 2 * ‖H‖ * κs * Δ * convFactor κs ^ (k - 1) ≤ ε →
      ‖g + H (s k) + μ k • s k‖ ≤ ε := by
    intro k hk hkG hA
    obtain ⟨hsΔ, hm⟩ := hmul k hk hkG
    have hμ := (neg_leftmost_lt_of_isTrustRegionMultiplier_krylov hH hg hk (hs k) hm).1
    have hκ := one_le_krylovCond (g := g) hH hμ
    have hq0 := convFactor_nonneg hκ
    have hq := convFactor_le_convFactor (hκs k hk hkG)
    have hΔ : 0 ≤ Δ := (norm_nonneg _).trans hsΔ
    refine ((krylov_residual_bound_trustRegion hH hg hk (hs k) hsΔ hm).trans ?_).trans hA
    have hκs0 : 0 ≤ κs := by linarith [hκs k hk hkG]
    gcongr
    exact hκs k hk hkG
  have hPG : ‖g + H (s G) + μ G • s G‖ ≤ ε := by
    rw [residual_eq_zero_of_grade_le hG le_rfl (hs G)
      ((hmul G hG le_rfl).2.galerkin_of_compressionL (hs G)), norm_zero]
    exact hε.le
  have hP' : ∀ k, 1 ≤ k → k ≤ G → 2 * ‖H‖ * κs * Δ / ε * convFactor κs ^ (k - 1) ≤ 1 →
      ‖g + H (s k) + μ k • s k‖ ≤ ε := fun k hk hkG hA => hP k hk hkG (by
    rw [div_mul_eq_mul_div, div_le_one hε] at hA; exact hA)
  obtain ⟨h1, h2⟩ := exists_le_min_of_geometric hG hP' hPG
  refine ⟨hP, hPG, fun hκ => h1 (convFactor_pos hκ) (convFactor_lt_one κs), fun hκ => h2 ?_⟩
  rw [hκ, convFactor_one]

end Residual

end Subproblem
