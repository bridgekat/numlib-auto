/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace` beside the least-squares material.
-/
import Mathlib.Analysis.Convex.Extrema
import Numlib.LinearAlgebra.Matrix.LeastSquares.Regularized
import Numlib.LinearAlgebra.Matrix.QR

/-!
# Constrained least squares

Let $A \in \mathbb{K}^{m \times n}$, $b \in \mathbb{K}^m$, $B \in \mathbb{K}^{p \times n}$ and
$d \in \mathbb{K}^p$, with $\mathbb{K}$ either $\mathbb{R}$ or $\mathbb{C}$. This module studies two
constrained least-squares problems of [golub2013matrix], §6.2: least squares with a quadratic
inequality constraint (LSQI), $\min \|Ax - b\|$ subject to $\|Bx - d\| \le \alpha$, and least
squares with linear equality constraints (LSE), $\min \|Ax - b\|$ subject to $Bx = d$. LSE is LSQI
with $\alpha = 0$.

For the sphere problem $\|x\| \le \alpha$, a feasible least-squares solution solves LSQI. Otherwise
every solution lies on the sphere $\|x\| = \alpha$, and the ridge solution
$x(\lambda) = (A^H A + \lambda I)^{-1} A^H b$ of norm $\alpha$ is a solution; the secular equation
$\|x(\lambda)\| = \alpha$ has exactly one positive root. No Lagrange multiplier theorem is used: the
inequality $\|Ay - b\|^2 + \lambda \|y\|^2 \ge \|Ax(\lambda) - b\|^2 + \lambda \alpha^2$ does the
work. For LSE, the module proves existence and uniqueness, the solution through a QR factorization
of $B^H$, the augmented system, the solution through the generalized singular value decomposition
(GSVD), and the convergence of the method of weighting.

## Main definitions

* `Matrix.IsLSQISolution`: $x$ minimizes $\|Ax - b\|$ subject to $\|Bx - d\| \le \alpha$.
* `Matrix.IsLSESolution`: $x$ minimizes $\|Ax - b\|$ subject to $Bx = d$.
* `Matrix.augmentedLSE`: the symmetric indefinite matrix $\begin{bmatrix} 0 & A^H & B^H \\ A & I & 0
  \\ B & 0 & 0 \end{bmatrix}$ of (6.2.10).
* `Matrix.penaltyLSE`: the solution $(A^H A + \lambda B^H B)^{-1} (A^H b + \lambda B^H d)$ of the
  method of weighting, (6.2.13).

## Main results

* `Matrix.isLSQISolution_zero_iff`: LSE is LSQI with $\alpha = 0$.
* `Matrix.isLSQISolution_of_isLeastSquaresSolution`: a feasible least-squares solution solves LSQI.
* `Matrix.IsLSQISolution.norm_eq_of_lt`: if $\alpha < \|A^+ b\|$, every solution of the sphere
  problem has $\|x\| = \alpha$.
* `Matrix.isLSQISolution_tikhonov`: a ridge solution $x(\lambda)$ with $\lambda > 0$ and
  $\|x(\lambda)\| = \alpha$ solves the sphere problem.
* `Matrix.existsUnique_norm_toEuclideanLin_tikhonov_eq`: for $0 < \alpha < \|A^+ b\|$, exactly one
  $\lambda > 0$ has $\|x(\lambda)\| = \alpha$.
* `Matrix.existsUnique_isLSESolution`: a consistent LSE problem has a solution, and it is unique if
  $\ker A \cap \ker B = 0$.
* `Matrix.isLSESolution_of_augmented`: a solution of the augmented system (6.2.10) gives an LSE
  solution.
* `Matrix.isUnit_augmentedLSE`: the augmented matrix is nonsingular if $A$ has full column rank and
  $B$ has full row rank.
* `Matrix.isLSESolution_of_isQR`: the LSE solution through the QR factorization of $B^H$, the
  derivation of Algorithm 6.2.2.
* `Matrix.isLSQISolution_iff_of_isGSVD`: LSQI in GSVD coordinates, (6.2.6).
* `Matrix.isLSESolution_sum_of_isGSVD`: the LSE solution as a combination of the columns of the GSVD
  factor $X$, (6.2.12).
* `Matrix.penaltyLSE_sub_eq_sum_of_isGSVD`: the error of the method of weighting in GSVD
  coordinates, (6.2.14).
* `Matrix.tendsto_penaltyLSE`: the method of weighting converges to the LSE solution as
  $\lambda \to \infty$.

## Implementation notes

* Vectors are elements of `EuclideanSpace`, and matrices act through `Matrix.toEuclideanLin`, as in
  `Numlib.LinearAlgebra.Matrix.LeastSquares`. The two problems are specifications in the style of
  `Matrix.IsLeastSquaresSolution`.
* The regularization parameter $\lambda$ is the Lean variable `μ`, because `λ` is a Lean keyword.
  The ridge solution $x(\lambda)$ is `Matrix.tikhonov A μ` applied to $b$.
* The GSVD statements use the block order of Theorem 6.1.1 of [golub2013matrix] (`Matrix.IsGSVD`).
  The source prints (6.2.12) and (6.2.14) in the block order of its third edition, and (6.2.14) has
  $\lambda^2$ where $\lambda$ is correct.
-/

open Filter Topology

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### The two problems -/

section Defs

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p] [DecidableEq n]

/-- Let $A \in \mathbb{K}^{m \times n}$, $b \in \mathbb{K}^m$, $B \in \mathbb{K}^{p \times n}$,
$d \in \mathbb{K}^p$ and $\alpha \in \mathbb{R}$. A vector $x \in \mathbb{K}^n$ is a solution of
**least squares with a quadratic inequality constraint** if $\|Bx - d\| \le \alpha$ and
$$\|Ax - b\| \le \|Ay - b\| \quad \text{for every } y \text{ with } \|By - d\| \le \alpha.$$
This is problem (6.2.5) of [golub2013matrix]. The sphere problem (6.2.1) is the case $B = I$,
$d = 0$. -/
structure IsLSQISolution (A : Matrix m n 𝕜) (b : EuclideanSpace 𝕜 m) (B : Matrix p n 𝕜)
    (d : EuclideanSpace 𝕜 p) (α : ℝ) (x : EuclideanSpace 𝕜 n) : Prop where
  /-- The solution is feasible: $\|Bx - d\| \le \alpha$. -/
  feasible : ‖toEuclideanLin B x - d‖ ≤ α
  /-- The solution is optimal: $\|Ax - b\| \le \|Ay - b\|$ for every feasible $y$. -/
  le : ∀ y, ‖toEuclideanLin B y - d‖ ≤ α → ‖toEuclideanLin A x - b‖ ≤ ‖toEuclideanLin A y - b‖

/-- Let $A \in \mathbb{K}^{m \times n}$, $b \in \mathbb{K}^m$, $B \in \mathbb{K}^{p \times n}$ and
$d \in \mathbb{K}^p$. A vector $x \in \mathbb{K}^n$ is a solution of **least squares with linear
equality constraints** if $Bx = d$ and
$$\|Ax - b\| \le \|Ay - b\| \quad \text{for every } y \text{ with } By = d.$$
This is problem (6.2.9) of [golub2013matrix]. -/
structure IsLSESolution (A : Matrix m n 𝕜) (b : EuclideanSpace 𝕜 m) (B : Matrix p n 𝕜)
    (d : EuclideanSpace 𝕜 p) (x : EuclideanSpace 𝕜 n) : Prop where
  /-- The solution is feasible: $Bx = d$. -/
  feasible : toEuclideanLin B x = d
  /-- The solution is optimal: $\|Ax - b\| \le \|Ay - b\|$ for every $y$ with $By = d$. -/
  le : ∀ y, toEuclideanLin B y = d → ‖toEuclideanLin A x - b‖ ≤ ‖toEuclideanLin A y - b‖

variable {A : Matrix m n 𝕜} {b : EuclideanSpace 𝕜 m} {B : Matrix p n 𝕜} {d : EuclideanSpace 𝕜 p}
  {x : EuclideanSpace 𝕜 n}

/-- A vector $x$ solves the LSQI problem with $\alpha = 0$ if and only if it solves the LSE problem
with the same data. This is stated in §6.2.3 of [golub2013matrix]. -/
theorem isLSQISolution_zero_iff : IsLSQISolution A b B d 0 x ↔ IsLSESolution A b B d x := by
  constructor
  · rintro ⟨hf, hle⟩
    exact ⟨sub_eq_zero.1 (norm_le_zero_iff.1 hf),
      fun y hy => hle y (by rw [hy, sub_self, norm_zero])⟩
  · rintro ⟨hf, hle⟩
    exact ⟨by rw [hf, sub_self, norm_zero],
      fun y hy => hle y (sub_eq_zero.1 (norm_le_zero_iff.1 hy))⟩

/-- If $x$ is a least-squares solution of $Ax = b$ and $\|Bx - d\| \le \alpha$, then $x$ solves the
LSQI problem. This is the remark of §6.2.1 of [golub2013matrix] that a least-squares solution
$x_{LS}$ with $\|x_{LS}\|_2 \le \alpha$ solves (6.2.1). -/
theorem isLSQISolution_of_isLeastSquaresSolution (h : IsLeastSquaresSolution A b x) {α : ℝ}
    (hx : ‖toEuclideanLin B x - d‖ ≤ α) : IsLSQISolution A b B d α x :=
  ⟨hx, fun y _ => h y⟩

omit [Fintype p] in
/-- Let $x$ solve the LSE problem, and let $z \in \ker A \cap \ker B$. Then $x + z$ also solves the
LSE problem. Hence the LSE solution is not unique if $\ker A \cap \ker B \ne 0$, as stated in
§6.2.3 of [golub2013matrix]. -/
theorem IsLSESolution.add_of_mem (h : IsLSESolution A b B d x) {z : EuclideanSpace 𝕜 n}
    (hz : z ∈ LinearMap.ker (toEuclideanLin A) ⊓ LinearMap.ker (toEuclideanLin B)) :
    IsLSESolution A b B d (x + z) := by
  obtain ⟨hA, hB⟩ := Submodule.mem_inf.1 hz
  rw [LinearMap.mem_ker] at hA hB
  refine ⟨by rw [map_add, hB, add_zero, h.feasible], fun y hy => ?_⟩
  rw [map_add, hA, add_zero]
  exact h.le y hy

omit [Fintype p] in
/-- If $x$ and $x'$ solve the same LSE problem and $\ker A \cap \ker B = 0$, then $x' = x$.

Two LSE solutions differ by an element of $\ker A \cap \ker B$: otherwise, by the parallelogram
law, their midpoint would have a smaller residual. -/
theorem IsLSESolution.eq_of_ker_inf_ker_eq_bot {x x' : EuclideanSpace 𝕜 n}
    (hsol : IsLSESolution A b B d x) (hx' : IsLSESolution A b B d x')
    (hAB : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥) : x' = x := by
  -- uniqueness through the parallelogram law
  have hv : ‖toEuclideanLin A x - b‖ = ‖toEuclideanLin A x' - b‖ :=
    le_antisymm (hsol.le x' hx'.feasible) (hx'.le x hsol.feasible)
  have hmid : toEuclideanLin B ((2⁻¹ : 𝕜) • (x + x')) = d := by
    rw [map_smul, map_add, hsol.feasible, hx'.feasible, ← two_smul 𝕜 d, smul_smul,
      inv_mul_cancel₀ two_ne_zero, one_smul]
  have hle := hsol.le _ hmid
  have hmid' : toEuclideanLin A ((2⁻¹ : 𝕜) • (x + x')) - b
      = (2⁻¹ : 𝕜) • ((toEuclideanLin A x - b) + (toEuclideanLin A x' - b)) := by
    rw [map_smul, map_add]
    module
  rw [hmid', norm_smul, norm_inv, RCLike.norm_ofNat] at hle
  have hpar := parallelogram_law_with_norm 𝕜 (toEuclideanLin A x - b) (toEuclideanLin A x' - b)
  have h2 : 2 * ‖toEuclideanLin A x - b‖
      ≤ ‖(toEuclideanLin A x - b) + (toEuclideanLin A x' - b)‖ := by linarith
  have hsq := mul_self_le_mul_self (by positivity) h2
  have hz : ‖(toEuclideanLin A x - b) - (toEuclideanLin A x' - b)‖ = 0 := by
    have h0 : ‖(toEuclideanLin A x - b) - (toEuclideanLin A x' - b)‖ *
        ‖(toEuclideanLin A x - b) - (toEuclideanLin A x' - b)‖ = 0 := by
      refine le_antisymm ?_ (mul_self_nonneg _)
      rw [← hv] at hpar
      nlinarith
    exact mul_self_eq_zero.1 h0
  have hA0 : toEuclideanLin A (x - x') = 0 := by
    rw [norm_eq_zero, sub_sub_sub_cancel_right] at hz
    rw [map_sub, hz]
  have hB0 : toEuclideanLin B (x - x') = 0 := by
    rw [map_sub, hsol.feasible, hx'.feasible, sub_self]
  have hmem : WithLp.ofLp (x - x') ∈ LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin := by
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · rw [LinearMap.mem_ker, mulVecLin_apply, ← ofLp_toEuclideanLin, hA0, WithLp.ofLp_zero]
    · rw [LinearMap.mem_ker, mulVecLin_apply, ← ofLp_toEuclideanLin, hB0, WithLp.ofLp_zero]
  rw [hAB, Submodule.mem_bot] at hmem
  have : x - x' = 0 := by simpa using congrArg (WithLp.toLp 2) hmem
  exact (sub_eq_zero.1 this).symm

end Defs

/-! ### Least squares over a sphere -/

section Sphere

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] [DecidableEq m]
  {A : Matrix m n 𝕜} {b : EuclideanSpace 𝕜 m} {x : EuclideanSpace 𝕜 n}

/-- The constraint $\|Ix - 0\| \le \alpha$ of the sphere problem is $\|x\| \le \alpha$. -/
private theorem norm_one_sub_zero (y : EuclideanSpace 𝕜 n) :
    ‖toEuclideanLin (1 : Matrix n n 𝕜) y - 0‖ = ‖y‖ := by
  rw [toEuclideanLin_one_apply, sub_zero]

omit [DecidableEq m] in
/-- If $\|x\| < \alpha$ and $x$ minimizes $\|Ay - b\|$ over the ball $\|y\| \le \alpha$, then $x$ is
a least-squares solution, because the objective is convex. -/
private theorem isLeastSquaresSolution_of_forall_norm_le {α : ℝ} (hx : ‖x‖ < α)
    (h : ∀ y : EuclideanSpace 𝕜 n, ‖y‖ ≤ α → ‖toEuclideanLin A x - b‖ ≤ ‖toEuclideanLin A y - b‖) :
    IsLeastSquaresSolution A b x := by
  have hconv : ConvexOn ℝ Set.univ fun y : EuclideanSpace 𝕜 n => ‖toEuclideanLin A y - b‖ := by
    refine ⟨convex_univ, fun y _ z _ s t hs ht hst => ?_⟩
    have e : toEuclideanLin A (s • y + t • z) - b
        = s • (toEuclideanLin A y - b) + t • (toEuclideanLin A z - b) := by
      rw [map_add, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, smul_sub, smul_sub]
      nth_rw 1 [← one_smul ℝ b, ← hst, add_smul]
      abel
    refine (e ▸ norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_smul, norm_smul, Real.norm_of_nonneg hs, Real.norm_of_nonneg ht, smul_eq_mul,
      smul_eq_mul]
  have hloc : IsLocalMin (fun y : EuclideanSpace 𝕜 n => ‖toEuclideanLin A y - b‖) x :=
    Filter.eventually_of_mem (Metric.ball_mem_nhds x (sub_pos.2 hx)) fun y hy => h y (by
      rw [Metric.mem_ball, dist_eq_norm] at hy
      linarith [norm_sub_norm_le y x])
  exact IsMinOn.of_isLocalMin_of_convex_univ hloc hconv

/-- Let $A \in \mathbb{K}^{m \times n}$, $b \in \mathbb{K}^m$ and $\alpha < \|A^+ b\|$. If $x$
solves the sphere problem $\min \|Ax - b\|$ subject to $\|x\| \le \alpha$, then
$$\|x\| = \alpha.$$
This is the statement after (6.2.3) of [golub2013matrix] that the solution of (6.2.1) is on the
boundary of the constraint sphere.

If $\|x\| < \alpha$, then $x$ minimizes the convex objective near $x$, hence everywhere, and
every least-squares solution has norm at least $\|A^+ b\|$. -/
theorem IsLSQISolution.norm_eq_of_lt {α : ℝ} (hα : α < ‖toEuclideanLin A.pinv b‖)
    (h : IsLSQISolution A b (1 : Matrix n n 𝕜) 0 α x) : ‖x‖ = α := by
  have hxα : ‖x‖ ≤ α := by simpa [norm_one_sub_zero] using h.feasible
  refine le_antisymm hxα (not_lt.1 fun hlt => ?_)
  have hls := isLeastSquaresSolution_of_forall_norm_le hlt fun y hy =>
    h.le y (by rw [norm_one_sub_zero]; exact hy)
  have := A.norm_pinv_le_of_normalEquations b (isLeastSquaresSolution_iff_normalEquations.1 hls)
  linarith

/-- Let $A \in \mathbb{K}^{m \times n}$, $b \in \mathbb{K}^m$ and $\lambda > 0$, and let
$x(\lambda) = (A^H A + \lambda I)^{-1} A^H b$ be the ridge solution. If
$\|x(\lambda)\| = \alpha$, then $x(\lambda)$ solves the sphere problem $\min \|Ax - b\|$ subject
to $\|x\| \le \alpha$. This is the statement of §6.2.1 of [golub2013matrix] that $x(\lambda_+)$
solves (6.2.1).

For feasible $y$, `Matrix.eq_toEuclideanLin_tikhonov_iff_isMinOn` gives $\|Ay - b\|^2 \ge
\|Ax(\lambda) - b\|^2 + \lambda (\alpha^2 - \|y\|^2) \ge \|Ax(\lambda) - b\|^2$. This is the
sufficient half of the Lagrange conditions, proved without the multiplier theorem. The ridge
solution is `Matrix.tikhonov A μ` applied to $b$. -/
theorem isLSQISolution_tikhonov {μ : ℝ} (hμ : 0 < μ) {α : ℝ}
    (hn : ‖toEuclideanLin (A.tikhonov μ) b‖ = α) :
    IsLSQISolution A b (1 : Matrix n n 𝕜) 0 α (toEuclideanLin (A.tikhonov μ) b) := by
  refine ⟨by rw [norm_one_sub_zero, hn], fun y hy => ?_⟩
  rw [norm_one_sub_zero] at hy
  have hmin := isMinOn_univ_iff.1 ((A.eq_toEuclideanLin_tikhonov_iff_isMinOn hμ b _).1 rfl) y
  rw [hn] at hmin
  have hy2 : ‖y‖ ^ 2 ≤ α ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hy 2
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  nlinarith

/-- Let $A \in \mathbb{K}^{m \times n}$, $b \in \mathbb{K}^m$ and $0 < \alpha < \|A^+ b\|$. Then
exactly one $\lambda > 0$ satisfies the secular equation
$$\|x(\lambda)\| = \alpha, \qquad x(\lambda) = (A^H A + \lambda I)^{-1} A^H b.$$
This is the statement of §6.2.1 of [golub2013matrix] that the secular function has a unique
positive root $\lambda_+$.

The norm $\|x(\lambda)\|$ decreases strictly and continuously from $\|A^+ b\|$ at $0^+$ to $0$
at $\infty$, so `existsUnique_pos_eq_of_strictAntiOn_Ioi` applies. -/
theorem existsUnique_norm_toEuclideanLin_tikhonov_eq {α : ℝ} (hα0 : 0 < α)
    (hα : α < ‖toEuclideanLin A.pinv b‖) :
    ∃! μ : ℝ, 0 < μ ∧ ‖toEuclideanLin (A.tikhonov μ) b‖ = α := by
  have h0 : Tendsto (fun μ => ‖toEuclideanLin (A.tikhonov μ) b‖) (𝓝[>] 0)
      (𝓝 ‖toEuclideanLin A.pinv b‖) := by
    have hc : Continuous fun M : Matrix n m 𝕜 => ‖toEuclideanLin M b‖ := by
      have : Continuous fun M : Matrix n m 𝕜 => toEuclideanLin M b :=
        (LinearMap.continuous_of_finiteDimensional
          (LinearMap.applyₗ (R := 𝕜) b ∘ₗ (toEuclideanLin (m := n) (n := m)).toLinearMap))
      exact continuous_norm.comp this
    exact (hc.tendsto _).comp A.tendsto_tikhonov_pinv
  have hAb : toEuclideanLin Aᴴ b ≠ 0 := by
    intro h
    have : toEuclideanLin A.pinv b = 0 := by
      rw [pinv_def, toEuclideanLin_mul_apply, h, map_zero]
    rw [this, norm_zero] at hα
    linarith
  exact existsUnique_pos_eq_of_strictAntiOn_Ioi (A.strictAntiOn_norm_toEuclideanLin_tikhonov hAb)
    (continuousOn_norm_toEuclideanLin_tikhonov A b) h0
    (A.tendsto_norm_toEuclideanLin_tikhonov_atTop b) hα0 hα

end Sphere

/-! ### Least squares with equality constraints -/

section LSE

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq m]
  [DecidableEq p] {A : Matrix m n 𝕜} {b : EuclideanSpace 𝕜 m} {B : Matrix p n 𝕜}
  {d : EuclideanSpace 𝕜 p}

omit [Fintype p] [DecidableEq m] [DecidableEq p] in
/-- Let $A \in \mathbb{K}^{m \times n}$, $b \in \mathbb{K}^m$, $B \in \mathbb{K}^{p \times n}$ and
$d \in \mathbb{K}^p$, and let $d$ lie in the range of $B$. Then the LSE problem
$\min \|Ax - b\|$ subject to $Bx = d$ has a solution. If in addition $\ker A \cap \ker B = 0$,
the solution is unique. This is discussed in §6.2.3–6.2.5 of [golub2013matrix].

For existence, let $B x_0 = d$ and $N = I - B^+ B$, whose range is $\ker B$. The feasible points
are the $x_0 + Nz$, so a least-squares solution $z_0$ of $(AN) z \approx b - A x_0$ gives the
solution $x_0 + N z_0$. For uniqueness, the parallelogram law shows that $A(x - x') = 0$ for two
solutions $x$ and $x'$. -/
theorem existsUnique_isLSESolution [Finite p]
    (hd : d ∈ LinearMap.range (toEuclideanLin B)) :
    (∃ x, IsLSESolution A b B d x) ∧
      (LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥ →
        ∃! x, IsLSESolution A b B d x) := by
  classical
  have := Fintype.ofFinite p
  obtain ⟨x₀, hx₀⟩ := hd
  set N : Matrix n n 𝕜 := 1 - B.pinv * B with hN
  have hBN : B * N = 0 := by rw [hN, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc,
    mul_pinv_mul_self, sub_self]
  have hNv : ∀ v : EuclideanSpace 𝕜 n, toEuclideanLin B v = 0 → toEuclideanLin N v = v := by
    intro v hv
    rw [hN, toEuclideanLin_sub_apply, toEuclideanLin_one_apply, toEuclideanLin_mul_apply, hv,
      map_zero, sub_zero]
  set c : EuclideanSpace 𝕜 m := b - toEuclideanLin A x₀ with hc
  set z₀ := toEuclideanLin (A * N).pinv c
  have hz₀ := (A * N).isLeastSquaresSolution_pinv c
  set x := x₀ + toEuclideanLin N z₀ with hx
  have hres : ∀ z,
      toEuclideanLin A (x₀ + toEuclideanLin N z) - b = toEuclideanLin (A * N) z - c := by
    intro z
    rw [hc, map_add, toEuclideanLin_mul_apply]
    abel
  have hsol : IsLSESolution A b B d x := by
    refine ⟨by rw [hx, map_add, hx₀, ← toEuclideanLin_mul_apply, hBN, toEuclideanLin_zero_apply,
      add_zero], fun y hy => ?_⟩
    have hy' : y = x₀ + toEuclideanLin N (y - x₀) := by
      rw [hNv _ (by rw [map_sub, hy, hx₀, sub_self]), add_sub_cancel]
    rw [hx, hres, hy', hres]
    exact hz₀ _
  exact ⟨⟨x, hsol⟩, fun hAB => ⟨x, hsol, fun x' hx' => hsol.eq_of_ker_inf_ker_eq_bot hx' hAB⟩⟩

/-- Let $A \in \mathbb{K}^{m \times n}$ and $B \in \mathbb{K}^{p \times n}$. The **augmented matrix
of the LSE problem** is the symmetric indefinite matrix
$$\begin{bmatrix} 0 & A^H & B^H \\ A & I & 0 \\ B & 0 & 0 \end{bmatrix}$$
of (6.2.10) of [golub2013matrix].

It is indexed by `n ⊕ (m ⊕ p)`. -/
def augmentedLSE (A : Matrix m n 𝕜) (B : Matrix p n 𝕜) : Matrix (n ⊕ (m ⊕ p)) (n ⊕ (m ⊕ p)) 𝕜 :=
  fromBlocks 0 (fromCols Aᴴ Bᴴ) (fromRows A B) (fromBlocks 1 0 0 0)

omit [DecidableEq n] [DecidableEq p] in
/-- The augmented matrix acts by
$$\begin{bmatrix} 0 & A^H & B^H \\ A & I & 0 \\ B & 0 & 0 \end{bmatrix} \begin{bmatrix} x \\ r
  \\ l \end{bmatrix} = \begin{bmatrix} A^H r + B^H l \\ Ax + r \\ Bx \end{bmatrix}.$$
-/
theorem augmentedLSE_mulVec (x : n → 𝕜) (r : m → 𝕜) (l : p → 𝕜) :
    augmentedLSE A B *ᵥ Sum.elim x (Sum.elim r l)
      = Sum.elim (Aᴴ *ᵥ r + Bᴴ *ᵥ l) (Sum.elim (A *ᵥ x + r) (B *ᵥ x)) := by
  rw [augmentedLSE, fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, zero_add, fromCols_mulVec,
    fromRows_mulVec, fromBlocks_mulVec, one_mulVec, zero_mulVec, add_zero]
  ext (_ | _ | _) <;> simp

omit [DecidableEq m] [DecidableEq p] in
/-- If $A^H r = -B^H l$ and $Bw = 0$, then $\langle r, Aw \rangle = 0$. -/
private theorem inner_mulVec_eq_zero {r : m → 𝕜} {l : p → 𝕜} {w : n → 𝕜}
    (h : Aᴴ *ᵥ r + Bᴴ *ᵥ l = 0) (hw : B *ᵥ w = 0) :
    inner 𝕜 (WithLp.toLp 2 r : EuclideanSpace 𝕜 m) (toEuclideanLin A (WithLp.toLp 2 w)) = 0 := by
  classical
  rw [← toEuclideanLin_conjTranspose_inner_left, toEuclideanLin_toLp,
    eq_neg_of_add_eq_zero_left h, WithLp.toLp_neg, inner_neg_left, ← toEuclideanLin_toLp,
    toEuclideanLin_conjTranspose_inner_left, toEuclideanLin_toLp, hw, WithLp.toLp_zero,
    inner_zero_right, neg_zero]

omit [DecidableEq p] in
/-- Let $A \in \mathbb{K}^{m \times n}$, $B \in \mathbb{K}^{p \times n}$, $b \in \mathbb{K}^m$ and
$d \in \mathbb{K}^p$. If $x$, $r$ and $l$ satisfy
$$\begin{bmatrix} 0 & A^H & B^H \\ A & I & 0 \\ B & 0 & 0 \end{bmatrix} \begin{bmatrix} x \\ r
  \\ l \end{bmatrix} = \begin{bmatrix} 0 \\ b \\ d \end{bmatrix},$$
then $x$ solves the LSE problem $\min \|Ax - b\|$ subject to $Bx = d$. This is the augmented
system (6.2.10) of [golub2013matrix], §6.2.4.

For feasible $y$, $Ay - b = A(y - x) - r$ and $\langle r, A(y - x) \rangle = -\langle l, B(y -
x) \rangle = 0$, so $\|Ay - b\|^2 = \|r\|^2 + \|A(y - x)\|^2$. -/
theorem isLSESolution_of_augmented {x : n → 𝕜} {r : m → 𝕜} {l : p → 𝕜} {b' : m → 𝕜}
    {d' : p → 𝕜}
    (h : augmentedLSE A B *ᵥ Sum.elim x (Sum.elim r l) = Sum.elim (0 : n → 𝕜) (Sum.elim b' d')) :
    IsLSESolution A (WithLp.toLp 2 b') B (WithLp.toLp 2 d') (WithLp.toLp 2 x) := by
  rw [augmentedLSE_mulVec] at h
  have h1 : Aᴴ *ᵥ r + Bᴴ *ᵥ l = 0 := funext fun i => congrFun h (Sum.inl i)
  have h2 : A *ᵥ x + r = b' := funext fun i => congrFun h (Sum.inr (Sum.inl i))
  have h3 : B *ᵥ x = d' := funext fun i => congrFun h (Sum.inr (Sum.inr i))
  refine ⟨by rw [toEuclideanLin_toLp, h3], fun y hy => ?_⟩
  set w : n → 𝕜 := WithLp.ofLp y - x with hw
  have hBw : B *ᵥ w = 0 := by
    have := congrArg WithLp.ofLp hy
    rw [ofLp_toEuclideanLin] at this
    rw [hw, mulVec_sub, this, h3, sub_self]
  have hr : toEuclideanLin A (WithLp.toLp 2 x) - WithLp.toLp 2 b' = -WithLp.toLp 2 r := by
    rw [← h2, toEuclideanLin_toLp, WithLp.toLp_add]
    abel
  have hy' : toEuclideanLin A y - WithLp.toLp 2 b'
      = toEuclideanLin A (WithLp.toLp 2 w) + (-WithLp.toLp 2 r) := by
    rw [← hr, hw, WithLp.toLp_sub, WithLp.toLp_ofLp, map_sub]
    abel
  have hinner := inner_mulVec_eq_zero h1 hBw
  rw [hr, hy']
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [norm_add_sq (𝕜 := 𝕜), inner_neg_right, ← inner_conj_symm, hinner]
  simp only [map_zero, neg_zero, mul_zero, add_zero]
  nlinarith [sq_nonneg ‖toEuclideanLin A (WithLp.toLp 2 w)‖]

/-- Let $A \in \mathbb{K}^{m \times n}$ have linearly independent columns, and let
$B \in \mathbb{K}^{p \times n}$ have linearly independent rows. Then the augmented matrix of the
LSE problem is nonsingular. This is the statement of §6.2.4 of [golub2013matrix] that the system
is nonsingular if both $A$ and $B$ have full rank.

If $A^H r + B^H l = 0$, $Ax + r = 0$ and $Bx = 0$, then $\|r\|^2 = -\langle r, Ax \rangle = 0$.
So $r = 0$ and $x = 0$, and then $B^H l = 0$ gives $l = 0$. -/
theorem isUnit_augmentedLSE (hA : LinearIndependent 𝕜 Aᵀ) (hB : LinearIndependent 𝕜 B) :
    IsUnit (augmentedLSE A B) := by
  have hAi : Function.Injective A.mulVec := mulVec_injective_iff.2 hA
  have hBi : Function.Injective B.vecMul := vecMul_injective_iff.2 hB
  refine mulVec_injective_iff_isUnit.1 fun u v huv => ?_
  rw [← sub_eq_zero]
  rw [← sub_eq_zero, ← mulVec_sub] at huv
  set w := u - v
  have hw : w = Sum.elim (w ∘ Sum.inl) (Sum.elim (w ∘ Sum.inr ∘ Sum.inl)
      (w ∘ Sum.inr ∘ Sum.inr)) := by
    ext (_ | _ | _) <;> rfl
  rw [hw, augmentedLSE_mulVec] at huv
  set x := w ∘ Sum.inl
  set r := w ∘ Sum.inr ∘ Sum.inl
  set l := w ∘ Sum.inr ∘ Sum.inr
  have h1 : Aᴴ *ᵥ r + Bᴴ *ᵥ l = 0 := funext fun i => congrFun huv (Sum.inl i)
  have h2 : A *ᵥ x + r = 0 := funext fun i => congrFun huv (Sum.inr (Sum.inl i))
  have h3 : B *ᵥ x = 0 := funext fun i => congrFun huv (Sum.inr (Sum.inr i))
  have hinner := inner_mulVec_eq_zero h1 h3
  have hr0 : r = 0 := by
    have hrA : r = -(A *ᵥ x) := eq_neg_of_add_eq_zero_right h2
    have : inner 𝕜 (WithLp.toLp 2 r : EuclideanSpace 𝕜 m) (WithLp.toLp 2 r) = 0 := by
      calc inner 𝕜 (WithLp.toLp 2 r : EuclideanSpace 𝕜 m) (WithLp.toLp 2 r)
          = inner 𝕜 (WithLp.toLp 2 r : EuclideanSpace 𝕜 m)
              (-toEuclideanLin A (WithLp.toLp 2 x)) := by
            rw [toEuclideanLin_toLp, ← WithLp.toLp_neg, ← hrA]
        _ = 0 := by rw [inner_neg_right, hinner, neg_zero]
    rw [inner_self_eq_zero, WithLp.toLp_eq_zero] at this
    exact this
  have hx0 : x = 0 := hAi (by rw [mulVec_zero]; rwa [hr0, add_zero] at h2)
  have hl0 : l = 0 := by
    rw [hr0, mulVec_zero, zero_add] at h1
    have hs : star l ᵥ* B = (0 : p → 𝕜) ᵥ* B := by
      rw [zero_vecMul]
      have := congrArg star h1
      rwa [star_mulVec, conjTranspose_conjTranspose, star_zero] at this
    exact star_eq_zero.1 (hBi hs)
  rw [hw, hx0, hr0, hl0]
  ext (_ | _ | _) <;> rfl

end LSE

/-! ### LSE through the QR factorization of $B^H$ -/

section QR

variable {m : Type*} [Fintype m] [DecidableEq m] {p n : ℕ}

omit [DecidableEq m] in
/-- Let $A \in \mathbb{K}^{m \times n}$, $b \in \mathbb{K}^m$, and let
$B \in \mathbb{K}^{p \times n}$ with $p \le n$ have linearly independent rows. Let $B^H = QR$ be
a full QR factorization, let $Q = [Q_1 \; Q_2]$ with $Q_1$ the first $p$ columns and $Q_2$ the
last $n - p$ columns, and let $R_1$ be the leading $p \times p$ block of $R$. Put
$y = (R_1^H)^{-1} d$, and let $z$ be a least-squares solution of
$$(A Q_2) z \approx b - A Q_1 y.$$
Then $Q_1 y + Q_2 z$ solves the LSE problem $\min \|Ax - b\|$ subject to $Bx = d$. This is the
derivation of Algorithm 6.2.2 of [golub2013matrix], §6.2.3.

Since $BQ = R^H = [R_1^H \; 0]$, the feasible points are exactly the $Q_1 y + Q_2 z'$, and there
the objective is $\|A Q_2 z' - (b - A Q_1 y)\|$. The blocks are `Q.firstColumns hpn`,
`Q.lastColumns (Nat.sub_le n p)` and `R.firstRows hpn`. -/
theorem isLSESolution_of_isQR {A : Matrix m (Fin n) 𝕜} {b : EuclideanSpace 𝕜 m}
    {B : Matrix (Fin p) (Fin n) 𝕜} {d : EuclideanSpace 𝕜 (Fin p)} (hpn : p ≤ n)
    (hB : LinearIndependent 𝕜 B) {Q : Matrix (Fin n) (Fin n) 𝕜} {R : Matrix (Fin n) (Fin p) 𝕜}
    (h : IsQR Bᴴ Q R) {z : EuclideanSpace 𝕜 (Fin (n - p))}
    (hz : IsLeastSquaresSolution (A * Q.lastColumns (Nat.sub_le n p))
      (b - toEuclideanLin (A * Q.firstColumns hpn) (toEuclideanLin ((R.firstRows hpn)ᴴ)⁻¹ d)) z) :
    IsLSESolution A b B d
      (toEuclideanLin (Q.firstColumns hpn) (toEuclideanLin ((R.firstRows hpn)ᴴ)⁻¹ d)
        + toEuclideanLin (Q.lastColumns (Nat.sub_le n p)) z) := by
  classical
  set Q₁ := Q.firstColumns hpn with hQ₁
  set Q₂ := Q.lastColumns (Nat.sub_le n p) with hQ₂
  set R₁ := R.firstRows hpn with hR₁
  set y := toEuclideanLin (R₁ᴴ)⁻¹ d with hy
  set c := b - toEuclideanLin (A * Q₁) y with hc
  have hQQ : Qᴴ * Q = 1 := by
    rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.1 h.mem_unitaryGroup
  have hBQ : B * Q = Rᴴ := by
    have hB' : B = Rᴴ * Qᴴ := by rw [← conjTranspose_mul, h.mul_eq, conjTranspose_conjTranspose]
    rw [hB', Matrix.mul_assoc, hQQ, Matrix.mul_one]
  have hBQ₁ : B * Q₁ = R₁ᴴ := by
    ext i j
    have := congrFun (congrFun hBQ i) (Fin.castLE hpn j)
    simp only [Matrix.mul_apply, conjTranspose_apply] at this
    simp only [hQ₁, hR₁, Matrix.mul_apply, firstColumns_apply, conjTranspose_apply, firstRows_apply]
    exact this
  have hBQ₂ : B * Q₂ = 0 := by
    ext i j
    have := congrFun (congrFun hBQ i) ⟨n - (n - p) + j, by omega⟩
    simp only [Matrix.mul_apply, conjTranspose_apply] at this
    simp only [hQ₂, Matrix.mul_apply, lastColumns_apply, Matrix.zero_apply]
    rw [this, h.apply_eq_zero _ i (by simp only; omega), star_zero]
  have hsplit : Q₁ * Q₁ᴴ + Q₂ * Q₂ᴴ = 1 :=
    firstColumns_mul_conjTranspose_add_lastColumns_mul_conjTranspose h.mem_unitaryGroup hpn
      (Nat.sub_le n p) (by omega)
  have hR₁u : IsUnit (R₁ᴴ).det := by
    have hBc : LinearIndependent 𝕜 (Bᴴ)ᵀ := by
      refine mulVec_injective_iff.1 fun v w hvw => ?_
      have hBi : Function.Injective B.vecMul := vecMul_injective_iff.2 hB
      have := congrArg star hvw
      simp only [star_mulVec, conjTranspose_conjTranspose] at this
      exact star_injective (hBi this)
    rw [det_conjTranspose]
    exact ((isUnit_iff_isUnit_det _).1 (h.isUnit_firstRows_of_linearIndependent hpn hBc)).star
  have hy' : toEuclideanLin R₁ᴴ y = d := by
    rw [hy, ← toEuclideanLin_mul_apply, mul_nonsing_inv _ hR₁u, toEuclideanLin_one_apply]
  -- the residual at `Q₁ y + Q₂ z'`
  have hres : ∀ z', toEuclideanLin A (toEuclideanLin Q₁ y + toEuclideanLin Q₂ z') - b
      = toEuclideanLin (A * Q₂) z' - c := by
    intro z'
    rw [hc, map_add, toEuclideanLin_mul_apply, toEuclideanLin_mul_apply]
    abel
  refine ⟨?_, fun y' hy'' => ?_⟩
  · rw [map_add, ← toEuclideanLin_mul_apply B Q₁, ← toEuclideanLin_mul_apply B Q₂, hBQ₁, hBQ₂,
      toEuclideanLin_zero_apply, add_zero, hy']
  · -- every feasible point is `Q₁ y + Q₂ w₂`
    have hdec : y' = toEuclideanLin Q₁ (toEuclideanLin Q₁ᴴ y')
        + toEuclideanLin Q₂ (toEuclideanLin Q₂ᴴ y') := by
      rw [← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply, ← LinearMap.add_apply,
        ← map_add, hsplit, toEuclideanLin_one_apply]
    have hw₁ : toEuclideanLin Q₁ᴴ y' = y := by
      have hBy : toEuclideanLin B y' = toEuclideanLin R₁ᴴ (toEuclideanLin Q₁ᴴ y') := by
        conv_lhs => rw [hdec]
        rw [map_add, ← toEuclideanLin_mul_apply B Q₁, ← toEuclideanLin_mul_apply B Q₂, hBQ₁,
          hBQ₂, toEuclideanLin_zero_apply, add_zero]
      rw [hy'', ← hy'] at hBy
      have := congrArg (toEuclideanLin (R₁ᴴ)⁻¹) hBy
      rw [← toEuclideanLin_mul_apply (R₁ᴴ)⁻¹ R₁ᴴ, ← toEuclideanLin_mul_apply (R₁ᴴ)⁻¹ R₁ᴴ,
        nonsing_inv_mul _ hR₁u, toEuclideanLin_one_apply, toEuclideanLin_one_apply] at this
      exact this.symm
    rw [hres, hdec, hw₁, hres]
    exact hz _

end QR

/-! ### Constrained least squares in GSVD coordinates -/

section GSVD

/-- For unitary $U$ and every $X$, $\|U^H M X y - U^H c\| = \|M(Xy) - c\|$. -/
private theorem norm_unitary_mul_mul_sub {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] {U : Matrix m m 𝕜} (hU : U ∈ unitaryGroup m 𝕜) (M : Matrix m n 𝕜)
    (X : Matrix n n 𝕜) (c : EuclideanSpace 𝕜 m) (y : EuclideanSpace 𝕜 n) :
    ‖toEuclideanLin (star U * M * X) y - toEuclideanLin (star U) c‖
      = ‖toEuclideanLin M (toEuclideanLin X y) - c‖ := by
  rw [toEuclideanLin_mul_apply, toEuclideanLin_mul_apply, ← map_sub,
    norm_toEuclideanLin_apply_of_mem_unitaryGroup (Unitary.star_mem hU)]

/-- Let $U_1 \in \mathbb{K}^{m \times m}$ and $U_2 \in \mathbb{K}^{q \times q}$ be unitary, and let
$X \in \mathbb{K}^{n \times n}$ be invertible. Then $y$ solves the LSQI problem with the data
$(U_1^H A X, U_1^H b, U_2^H B X, U_2^H d, \alpha)$ if and only if $Xy$ solves the LSQI problem
with the data $(A, b, B, d, \alpha)$. -/
theorem isLSQISolution_unitary_mul_mul_iff {m n q : Type*} [Fintype m] [Fintype n] [Fintype q]
    [DecidableEq m] [DecidableEq n] [DecidableEq q] {A : Matrix m n 𝕜} {b : EuclideanSpace 𝕜 m}
    {B : Matrix q n 𝕜} {d : EuclideanSpace 𝕜 q} {α : ℝ} {U₁ : Matrix m m 𝕜}
    {U₂ : Matrix q q 𝕜} {X : Matrix n n 𝕜} (hU₁ : U₁ ∈ unitaryGroup m 𝕜)
    (hU₂ : U₂ ∈ unitaryGroup q 𝕜) (hX : IsUnit X) (y : EuclideanSpace 𝕜 n) :
    IsLSQISolution (star U₁ * A * X) (toEuclideanLin (star U₁) b) (star U₂ * B * X)
        (toEuclideanLin (star U₂) d) α y ↔ IsLSQISolution A b B d α (toEuclideanLin X y) := by
  have hXX : ∀ v, toEuclideanLin X (toEuclideanLin X⁻¹ v) = v := fun v => by
    rw [← toEuclideanLin_mul_apply, mul_nonsing_inv _ ((isUnit_iff_isUnit_det X).1 hX),
      toEuclideanLin_one_apply]
  constructor
  · rintro ⟨hf, hle⟩
    refine ⟨by rwa [norm_unitary_mul_mul_sub hU₂] at hf, fun v hv => ?_⟩
    have := hle (toEuclideanLin X⁻¹ v) (by rwa [norm_unitary_mul_mul_sub hU₂, hXX])
    rwa [norm_unitary_mul_mul_sub hU₁, norm_unitary_mul_mul_sub hU₁, hXX] at this
  · rintro ⟨hf, hle⟩
    refine ⟨by rwa [norm_unitary_mul_mul_sub hU₂], fun v hv => ?_⟩
    rw [norm_unitary_mul_mul_sub hU₁, norm_unitary_mul_mul_sub hU₁]
    exact hle _ (by rwa [norm_unitary_mul_mul_sub hU₂] at hv)

variable {m₁ m₂ n : ℕ} {A : Matrix (Fin m₁) (Fin n) 𝕜} {B : Matrix (Fin m₂) (Fin n) 𝕜}
  {U₁ : Matrix (Fin m₁) (Fin m₁) 𝕜} {U₂ : Matrix (Fin m₂) (Fin m₂) 𝕜}
  {X : Matrix (Fin n) (Fin n) 𝕜} {α' β' : ℕ → ℝ}

/-- Let $A \in \mathbb{K}^{m_1 \times n}$ and $B \in \mathbb{K}^{m_2 \times n}$ have the GSVD
$U_1^H A X = D_A$, $U_2^H B X = D_B$, and let $b \in \mathbb{K}^{m_1}$, $d \in \mathbb{K}^{m_2}$
and $\alpha \in \mathbb{R}$. Then $x$ solves $\min \|Ax - b\|$ subject to
$\|Bx - d\| \le \alpha$ if and only if $X^{-1} x$ solves
$$\min \|D_A y - \tilde b\| \quad \text{subject to} \quad \|D_B y - \tilde d\| \le \alpha,
  \qquad \tilde b = U_1^H b, \quad \tilde d = U_2^H d.$$
This is (6.2.6) of [golub2013matrix], and (6.2.11) for $\alpha = 0$.

The GSVD is `Matrix.IsGSVD`. The transformed matrices appear as `star U₁ * A * X` and
`star U₂ * B * X`. -/
theorem isLSQISolution_iff_of_isGSVD (h : IsGSVD A B U₁ U₂ X α' β') {b : EuclideanSpace 𝕜 (Fin m₁)}
    {d : EuclideanSpace 𝕜 (Fin m₂)} {α : ℝ} {x : EuclideanSpace 𝕜 (Fin n)} :
    IsLSQISolution A b B d α x ↔
      IsLSQISolution (star U₁ * A * X) (toEuclideanLin (star U₁) b) (star U₂ * B * X)
        (toEuclideanLin (star U₂) d) α (toEuclideanLin X⁻¹ x) := by
  rw [isLSQISolution_unitary_mul_mul_iff h.mem_unitaryGroup_left₁ h.mem_unitaryGroup_left₂
      h.isUnit,
    ← toEuclideanLin_mul_apply,
    mul_nonsing_inv _ ((isUnit_iff_isUnit_det X).1 h.isUnit), toEuclideanLin_one_apply]

end GSVD

/-! ### The LSE solution and the method of weighting in GSVD coordinates -/

section GSVDLSE

/-- Let $n \le m_1$, $\tilde b \in \mathbb{K}^{m_1}$, $\tilde d \in \mathbb{K}^p$ and
$\beta \colon \mathbb{N} \to \mathbb{R}$. The **coefficients of the LSE solution in GSVD
coordinates** are, for $i = 1, \dots, n$,
$$c_i = \tilde b_i \quad (i \le n - p), \qquad c_i = \tilde d_{i - (n - p)} / \beta_i \quad (i >
  n - p).$$
These are the coefficients of (6.2.12) of [golub2013matrix], in the block order of Theorem
6.1.1: the first $n - p$ columns belong to $A$ alone ($\alpha_i = 1$), and the last $p$ columns
are shared.

Lean indices start at $0$, so the first case is `i < n - p`. If $\beta_i = 0$, the quotient is
$0$. -/
noncomputable def lseGSVDCoeff {m₁ p n : ℕ} (hnm : n ≤ m₁) (bt : Fin m₁ → 𝕜) (dt : Fin p → 𝕜)
    (β : ℕ → ℝ) (i : Fin n) : 𝕜 :=
  if h : (i : ℕ) < n - p then bt ⟨i, lt_of_lt_of_le i.isLt hnm⟩
  else dt ⟨(i : ℕ) - (n - p), by have := i.isLt; omega⟩ / (β i : 𝕜)

variable {m₁ p n : ℕ} {A : Matrix (Fin m₁) (Fin n) 𝕜} {B : Matrix (Fin p) (Fin n) 𝕜}
  {U₁ : Matrix (Fin m₁) (Fin m₁) 𝕜} {U₂ : Matrix (Fin p) (Fin p) 𝕜}
  {X : Matrix (Fin n) (Fin n) 𝕜} {α β : ℕ → ℝ}

/-- For $X \in \mathbb{K}^{n \times n}$ with columns $x_i$, $\sum_i y_i x_i = Xy$. -/
private theorem sum_smul_col_eq_mulVec {n : ℕ} (X : Matrix (Fin n) (Fin n) 𝕜) (y : Fin n → 𝕜) :
    ∑ i, y i • X.col i = X *ᵥ y := by
  simp only [mulVec_eq_sum, op_smul_eq_smul]
  rfl

/-- Let $A \in \mathbb{K}^{m_1 \times n}$ with $n \le m_1$, and let $B \in \mathbb{K}^{p \times n}$
have linearly independent rows, with $\ker A \cap \ker B = 0$. Let $U_1^H A X = D_A$,
$U_2^H B X = D_B$ be a GSVD with the numbers $\alpha_i$, $\beta_i$, let $x_1, \dots, x_n$ be the
columns of $X$, and let $\tilde b = U_1^H b$ and $\tilde d = U_2^H d$. Then
$$x = \sum_{i = 1}^{n - p} \tilde b_i x_i + \sum_{i = n - p + 1}^{n} \frac{\tilde d_{i - (n -
  p)}}{\beta_i} x_i$$
solves the LSE problem $\min \|Ax - b\|$ subject to $Bx = d$. This is (6.2.12) of
[golub2013matrix], in the block order of Theorem 6.1.1.

The source prints $\sum_{i \le m_2} (\tilde d_i / \beta_i) x_i + \sum_{i > m_2} (\tilde b_i /
\alpha_i) x_i$, in the block order of its third edition; here the columns of $A$ alone have
$\alpha_i = 1$. The solution is unique by `Matrix.IsLSESolution.eq_of_ker_inf_ker_eq_bot`. In
GSVD coordinates the constraint fixes the coordinates on the shared columns, and
$y_i = \tilde b_i$ minimizes the objective on the others. The coefficients are
`Matrix.lseGSVDCoeff`, and Lean indices start at $0$. -/
theorem isLSESolution_sum_of_isGSVD (h : IsGSVD A B U₁ U₂ X α β) (hnm : n ≤ m₁)
    (hB : LinearIndependent 𝕜 B)
    (hAB : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥)
    (b : EuclideanSpace 𝕜 (Fin m₁)) (d : EuclideanSpace 𝕜 (Fin p)) :
    IsLSESolution A b B d (WithLp.toLp 2 (∑ i : Fin n,
      lseGSVDCoeff hnm (toEuclideanLin (star U₁) b) (toEuclideanLin (star U₂) d) β i •
        X.col i)) := by
  classical
  obtain ⟨hrn, hpn, hβ⟩ := h.rank_eq_and_ne_zero hB hAB
  set bt := toEuclideanLin (star U₁) b with hbt
  set dt := toEuclideanLin (star U₂) d with hdt
  set y : Fin n → 𝕜 := lseGSVDCoeff hnm bt dt β with hy
  rw [sum_smul_col_eq_mulVec, ← toEuclideanLin_toLp, ← isLSQISolution_zero_iff,
    ← isLSQISolution_unitary_mul_mul_iff h.mem_unitaryGroup_left₁ h.mem_unitaryGroup_left₂
      h.isUnit, isLSQISolution_zero_iff, h.star_mul_mul₁, h.star_mul_mul₂, hrn]
  have hpure : ∀ i : Fin n, (i : ℕ) < n - p → α i = 1 := fun i hi =>
    (h.eq_one_and_eq_zero_of_lt i (by rw [hrn]; exact hi)).1
  -- the constraint in coordinates
  have hfeas : ∀ y' : Fin n → 𝕜,
      toEuclideanLin (shiftedRectDiagonal (n - p) fun i => ((β i : ℝ) : 𝕜)) (WithLp.toLp 2 y')
        = dt ↔ ∀ j : Fin n, n - p ≤ (j : ℕ) → y' j = y j := by
    intro y'
    constructor
    · intro hc j hj
      obtain ⟨k, hkdef⟩ : ∃ k : Fin p, (k : ℕ) = j - (n - p) := ⟨⟨j - (n - p), by omega⟩, rfl⟩
      have hk : (k : ℕ) + (n - p) < n := by omega
      have hkj : (⟨(k : ℕ) + (n - p), hk⟩ : Fin n) = j := Fin.ext (by simp only; omega)
      have hkj' : (k : ℕ) + (n - p) = j := by omega
      have := congrArg (fun v : EuclideanSpace 𝕜 (Fin p) => WithLp.ofLp v k) hc
      simp only [ofLp_toEuclideanLin,] at this
      rw [shiftedRectDiagonal_mulVec _ _ _ _ hk, hkj, hkj'] at this
      have hnlt : ¬ (j : ℕ) < n - p := by omega
      simp only [hy, lseGSVDCoeff, hnlt, ↓reduceDIte]
      rw [eq_div_iff (RCLike.ofReal_ne_zero.2 (hβ j hj)), mul_comm, this]
      exact congrArg (fun i => WithLp.ofLp dt i) (Fin.ext (by simp only; omega))
    · intro hc
      ext k
      have hk : (k : ℕ) + (n - p) < n := by omega
      simp only [ofLp_toEuclideanLin]
      rw [shiftedRectDiagonal_mulVec _ _ _ _ hk, hc _ (Nat.le_add_left _ _)]
      have hnlt : ¬ ((k : ℕ) + (n - p) < n - p) := by omega
      simp only [hy, lseGSVDCoeff, hnlt, ↓reduceDIte]
      rw [mul_div_cancel₀ _
        (RCLike.ofReal_ne_zero.2 (hβ ⟨(k : ℕ) + (n - p), hk⟩ (Nat.le_add_left _ _)))]
      exact congrArg (fun i => WithLp.ofLp dt i) (Fin.ext (by simp only; omega))
  refine ⟨(hfeas y).2 fun _ _ => rfl, fun y' hy' => ?_⟩
  have hy'' := (hfeas (WithLp.ofLp y')).1 (by rwa [WithLp.toLp_ofLp])
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [PiLp.sub_apply, ofLp_toEuclideanLin]
  by_cases hin : (i : ℕ) < n
  · rw [rectDiagonal_mulVec _ _ _ hin, rectDiagonal_mulVec _ _ _ hin]
    by_cases hip : (i : ℕ) < n - p
    · have : y ⟨i, hin⟩ = (star U₁ *ᵥ WithLp.ofLp b) i := by
        simp only [hy, lseGSVDCoeff, hip, ↓reduceDIte]
        rfl
      rw [hpure ⟨i, hin⟩ hip, RCLike.ofReal_one, one_mul, one_mul, this, sub_self, norm_zero]
      exact le_trans (zero_pow two_ne_zero).le (sq_nonneg _)
    · rw [hy'' ⟨i, hin⟩ (by simp only; omega)]
  · rw [rectDiagonal_mulVec_of_le _ _ _ (not_lt.1 hin),
      rectDiagonal_mulVec_of_le _ _ _ (not_lt.1 hin)]

/-- Let $A \in \mathbb{K}^{m \times n}$, $B \in \mathbb{K}^{q \times n}$, $b \in \mathbb{K}^m$,
$d \in \mathbb{K}^q$ and $\lambda \in \mathbb{R}$. The **method of weighting** gives the vector
$$x(\lambda) = (A^H A + \lambda B^H B)^{-1} (A^H b + \lambda B^H d).$$
It solves the normal equations of the weighted problem
$\min \|Ax - b\|^2 + \lambda \|Bx - d\|^2$, which is the stacked least-squares problem (6.2.13)
of [golub2013matrix], §6.2.6 (`Matrix.isLeastSquaresSolution_fromRows_iff`).

If $A^H A + \lambda B^H B$ is singular, the Lean inverse is $0$ and $x(\lambda) = 0$. -/
noncomputable def penaltyLSE {m n q : Type*} [Fintype m] [Fintype n] [Fintype q] [DecidableEq n]
    [DecidableEq m] [DecidableEq q] (A : Matrix m n 𝕜) (B : Matrix q n 𝕜)
    (b : EuclideanSpace 𝕜 m) (d : EuclideanSpace 𝕜 q) (μ : ℝ) : EuclideanSpace 𝕜 n :=
  toEuclideanLin (Aᴴ * A + (μ : 𝕜) • (Bᴴ * B))⁻¹
    (toEuclideanLin Aᴴ b + (μ : 𝕜) • toEuclideanLin Bᴴ d)

/-- Let $n \le m_1$, $\tilde b \in \mathbb{K}^{m_1}$, $\tilde d \in \mathbb{K}^p$,
$\alpha, \beta \colon \mathbb{N} \to \mathbb{R}$ and $\lambda \in \mathbb{R}$. The
**coefficients of the error of the method of weighting** are, for $i = 1, \dots, n$, $e_i = 0$
if $i \le n - p$, and
$$e_i = \frac{\alpha_i (\beta_i \tilde b_i - \alpha_i \tilde d_{i - (n - p)})}{\beta_i
  (\alpha_i^2 + \lambda \beta_i^2)} \quad \text{if } i > n - p.$$
These are the coefficients of (6.2.14) of [golub2013matrix], with $\lambda$ in place of the
printed $\lambda^2$.

Lean indices start at $0$, so the first case is `i < n - p`. A quotient with zero denominator is
$0$. -/
noncomputable def penaltyGSVDCoeff {m₁ p n : ℕ} (hnm : n ≤ m₁) (bt : Fin m₁ → 𝕜) (dt : Fin p → 𝕜)
    (α β : ℕ → ℝ) (μ : ℝ) (i : Fin n) : 𝕜 :=
  if h : (i : ℕ) < n - p then 0
  else (α i : 𝕜) * ((β i : 𝕜) * bt ⟨i, lt_of_lt_of_le i.isLt hnm⟩
      - (α i : 𝕜) * dt ⟨(i : ℕ) - (n - p), by have := i.isLt; omega⟩)
    / ((β i : 𝕜) * ((α i : 𝕜) ^ 2 + (μ : 𝕜) * (β i : 𝕜) ^ 2))

/-- Let $A$, $B$, the GSVD and $x$ be as in `Matrix.isLSESolution_sum_of_isGSVD`, and let
$\lambda > 0$. Then the vector $x(\lambda)$ of the method of weighting satisfies
$$x(\lambda) - x = \sum_{i = n - p + 1}^{n} \frac{\alpha_i (\beta_i \tilde b_i - \alpha_i \tilde
  d_{i - (n - p)})}{\beta_i (\alpha_i^2 + \lambda \beta_i^2)} x_i.$$
This is (6.2.14) of [golub2013matrix].

The source prints $\lambda^2$ where $\lambda$ is correct, writes $u_i^T b$ and $v_i^T d$ for
$\tilde b_i$ and $\tilde d_i$, and sums to $p$ in the block order of its third edition. In GSVD
coordinates, $y_i(\lambda) = (\alpha_i \tilde b_i + \lambda \beta_i \tilde d_{i - (n - p)}) /
(\alpha_i^2 + \lambda \beta_i^2)$ on the shared columns and $y_i(\lambda) = \tilde b_i$ on the
others (`Matrix.IsGSVD.inv_gram_add_smul_gram_eq`). The coefficients are
`Matrix.penaltyGSVDCoeff`. -/
theorem penaltyLSE_sub_eq_sum_of_isGSVD (h : IsGSVD A B U₁ U₂ X α β) (hnm : n ≤ m₁)
    (hB : LinearIndependent 𝕜 B)
    (hAB : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥)
    (b : EuclideanSpace 𝕜 (Fin m₁)) (d : EuclideanSpace 𝕜 (Fin p)) {μ : ℝ} (hμ : 0 < μ) :
    penaltyLSE A B b d μ - WithLp.toLp 2 (∑ i : Fin n,
        lseGSVDCoeff hnm (toEuclideanLin (star U₁) b) (toEuclideanLin (star U₂) d) β i • X.col i)
      = WithLp.toLp 2 (∑ i : Fin n, penaltyGSVDCoeff hnm (toEuclideanLin (star U₁) b)
          (toEuclideanLin (star U₂) d) α β μ i • X.col i) := by
  classical
  obtain ⟨hrn, hpn, hβ⟩ := h.rank_eq_and_ne_zero hB hAB
  set bt := toEuclideanLin (star U₁) b with hbt
  set dt := toEuclideanLin (star U₂) d with hdt
  have hpure : ∀ i : Fin n, (i : ℕ) < n - p → α i = 1 ∧ β i = 0 := fun i hi =>
    h.eq_one_and_eq_zero_of_lt i (by rw [hrn]; exact hi)
  have hd0 : ∀ i : Fin n, α i ^ 2 + μ * β i ^ 2 ≠ 0 := fun i =>
    h.sq_add_smul_sq_ne_zero hμ (by rw [hrn]; exact i.isLt)
  have hXB := h.conjTranspose_mul_conjTranspose_right
  rw [hrn] at hXB
  rw [penaltyLSE, h.inv_gram_add_smul_gram_eq hnm μ hd0, toEuclideanLin_mul_apply,
    toEuclideanLin_mul_apply, map_add, map_smul, ← toEuclideanLin_mul_apply Xᴴ,
    h.conjTranspose_mul_conjTranspose_left,
    ← toEuclideanLin_mul_apply Xᴴ, hXB, toEuclideanLin_mul_apply, toEuclideanLin_mul_apply,
    sum_smul_col_eq_mulVec, sum_smul_col_eq_mulVec, toEuclideanLin_apply, ← WithLp.toLp_sub,
    ← mulVec_sub]
  congr 2
  funext i
  simp only [Pi.sub_apply, WithLp.ofLp_add, WithLp.ofLp_smul, ofLp_toEuclideanLin,
    mulVec_diagonal, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    rectDiagonal_mulVec _ _ _ (lt_of_lt_of_le i.isLt hnm),
    conjTranspose_shiftedRectDiagonal_mulVec, lseGSVDCoeff, penaltyGSVDCoeff, ← hbt, ← hdt]
  by_cases hi : (i : ℕ) < n - p
  · obtain ⟨hα1, hβ0⟩ := hpure i hi
    simp [hi, hα1, hβ0]
  · have hn : n - p ≤ (i : ℕ) ∧ (i : ℕ) - (n - p) < p := ⟨by omega, by omega⟩
    simp only [hn, hi, and_self, ↓reduceDIte, ↓reduceDIte]
    have hb : ((β i : ℝ) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 (hβ i (by omega))
    have hd : ((α i : ℝ) : 𝕜) ^ 2 + (μ : 𝕜) * ((β i : ℝ) : 𝕜) ^ 2 ≠ 0 := by
      have := RCLike.ofReal_ne_zero (K := 𝕜).2 (hd0 i)
      push_cast at this
      exact this
    push_cast
    simp only [RCLike.star_def, RCLike.conj_ofReal]
    field_simp
    ring

/-- Let $A \in \mathbb{K}^{m_1 \times n}$ with $n \le m_1$, and let $B \in \mathbb{K}^{p \times n}$
have linearly independent rows, with $\ker A \cap \ker B = 0$. If $x$ solves the LSE problem
$\min \|Ax - b\|$ subject to $Bx = d$, then the vectors $x(\lambda)$ of the method of weighting
converge to $x$:
$$x(\lambda) \to x \quad \text{as } \lambda \to \infty.$$
This is stated in §6.2.6 of [golub2013matrix].

A GSVD exists (`Matrix.exists_isGSVD`), $x$ is the solution of
`Matrix.isLSESolution_sum_of_isGSVD`, and the coefficients of
`Matrix.penaltyLSE_sub_eq_sum_of_isGSVD` are $O(1/\lambda)$. -/
theorem tendsto_penaltyLSE (hnm : n ≤ m₁) (hB : LinearIndependent 𝕜 B)
    (hAB : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥)
    {b : EuclideanSpace 𝕜 (Fin m₁)} {d : EuclideanSpace 𝕜 (Fin p)} {x : EuclideanSpace 𝕜 (Fin n)}
    (hx : IsLSESolution A b B d x) : Tendsto (penaltyLSE A B b d) atTop (𝓝 x) := by
  classical
  obtain ⟨U₁, U₂, X, α, β, h⟩ := exists_isGSVD hnm A B
  obtain ⟨hrn, hpn, hβ⟩ := h.rank_eq_and_ne_zero hB hAB
  have hx' := (isLSESolution_sum_of_isGSVD h hnm hB hAB b d).eq_of_ker_inf_ker_eq_bot hx hAB
  set bt := toEuclideanLin (star U₁) b
  set dt := toEuclideanLin (star U₂) d
  have hc : ∀ i : Fin n, Tendsto (fun μ : ℝ => penaltyGSVDCoeff hnm bt dt α β μ i) atTop (𝓝 0) := by
    intro i
    by_cases hi : (i : ℕ) < n - p
    · simp only [penaltyGSVDCoeff, hi, ↓reduceDIte]
      exact tendsto_const_nhds
    · simp only [penaltyGSVDCoeff, hi, ↓reduceDIte]
      have hb : 0 < β i := lt_of_le_of_ne (h.nonneg i).2 (hβ i (by omega)).symm
      have hr : Tendsto (fun μ : ℝ => ((β i * (α i ^ 2 + μ * β i ^ 2))⁻¹ : ℝ)) atTop (𝓝 0) := by
        refine Tendsto.inv_tendsto_atTop (Tendsto.const_mul_atTop (by positivity) ?_)
        exact tendsto_atTop_add_const_left _ _
          (Tendsto.atTop_mul_const (by positivity) tendsto_id)
      have hr' := ((RCLike.continuous_ofReal (K := 𝕜)).tendsto 0).comp hr
      rw [RCLike.ofReal_zero] at hr'
      have := hr'.const_mul ((α i : 𝕜) * ((β i : 𝕜) * bt ⟨i, lt_of_lt_of_le i.isLt hnm⟩
        - (α i : 𝕜) * dt ⟨i - (n - p), by omega⟩))
      rw [mul_zero] at this
      refine this.congr fun μ => ?_
      simp only [Function.comp_apply]
      push_cast
      rw [div_eq_mul_inv]
  have hsum : Tendsto (fun μ : ℝ => WithLp.toLp 2 (∑ i : Fin n,
      penaltyGSVDCoeff hnm bt dt α β μ i • X.col i) : ℝ → EuclideanSpace 𝕜 (Fin n)) atTop
        (𝓝 0) := by
    have : Tendsto (fun μ : ℝ => ∑ i : Fin n, penaltyGSVDCoeff hnm bt dt α β μ i • X.col i)
        atTop (𝓝 0) := by
      have := tendsto_finsetSum (Finset.univ : Finset (Fin n)) fun i _ =>
        (hc i).smul_const (X.col i)
      simpa using this
    have hc' := ((PiLp.continuous_toLp 2 _).tendsto 0).comp this
    rw [WithLp.toLp_zero] at hc'
    exact hc'
  have := hsum.const_add x
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with μ hμ
  rw [← penaltyLSE_sub_eq_sum_of_isGSVD h hnm hB hAB b d hμ, ← hx']
  abel

end GSVDLSE

end Matrix
