/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Numlib.Analysis.InnerProductSpace.Basic
import Numlib.LinearAlgebra.Matrix.GSVD
import Numlib.LinearAlgebra.Matrix.LeastSquares.Weighted

/-!
# Regularized least squares

Let $A \in \mathbb{K}^{m \times n}$ and $b \in \mathbb{K}^m$, with $\mathbb{K}$ either $\mathbb{R}$
or $\mathbb{C}$, and let $\alpha > 0$. **Tikhonov regularization** replaces the least-squares
problem $Ax \approx b$ by the minimization of $\|Ax - b\|^2 + \alpha \|x\|^2$. Its unique solution
is the **ridge regression** solution $x(\alpha) = (\alpha I + A^H A)^{-1} A^H b$. The **general
form** minimizes $\|Ax - b\|^2 + \alpha \|Bx\|^2$ for a second matrix
$B \in \mathbb{K}^{p \times n}$, and its solution is $(A^H A + \alpha B^H B)^{-1} A^H b$ when
$\ker A \cap \ker B = 0$. The presentation follows [kress1998numerical], §5.3, and
[golub2013matrix], §5.3, §6.1 and §6.2.

The module proves that the regularized normal equations characterize the minimizers, the discrepancy
principle and its regularity, and the behaviour of $\|x(\alpha)\|$ in $\alpha$: it decreases
continuously from $\|A^+ b\|$ at $0^+$ to $0$ at $\infty$, and $x(\alpha) \to A^+ b$ as
$\alpha \to 0^+$. It expands $x(\alpha)$, $A^+ b$ and the residuals in a singular value
decomposition $U^H A V = \Sigma$, and the general form in a generalized singular value decomposition
(GSVD). Over $\mathbb{R}$, it gives the leave-one-out formulas of cross-validation. Below, $w_i$ are
the right singular vectors and $\sigma_i$ the singular values of $A$, indexed by the columns of $A$
and in no particular order, and $u_i$, $v_i$ are the columns of $U$ and $V$.

## Main definitions

* `Matrix.tikhonov`: the Tikhonov matrix $(\alpha I + A^H A)^{-1} A^H$.
* `Matrix.generalFormTikhonov`: the general-form matrix $(A^H A + \alpha B^H B)^{-1} A^H$.

## Main results

* `existsUnique_pos_eq_of_strictMonoOn_Ioi`: a continuous strictly increasing function on
  $(0, \infty)$ takes every value between its two limits exactly once.
* `Matrix.norm_sub_sq_add_mul_norm_sq_eq_of_gram_add_smul_gram`: the expansion of
  $\|Ax - b\|^2 + \alpha \|Bx\|^2$ around a solution of $(A^H A + \alpha B^H B) z = A^H b$.
* `Matrix.tikhonov_unique`: for $\alpha > 0$, $x(\alpha)$ is the unique solution of
  $\alpha x + A^H A x = A^H b$.
* `Matrix.norm_sub_sq_add_mul_norm_sq_tikhonov_le`: for $\alpha > 0$, $x(\alpha)$ minimizes
  $\|Ax - b\|^2 + \alpha \|x\|^2$.
* `Matrix.exists_discrepancy_tikhonov`: the discrepancy principle, Theorem 5.10 of
  [kress1998numerical].
* `Matrix.tendsto_tikhonov_of_norm_toEuclideanLin_sub_eq`: the discrepancy principle is regular,
  Theorem 5.10 of [kress1998numerical].
* `Matrix.antitoneOn_norm_toEuclideanLin_tikhonov`: $\alpha \mapsto \|x(\alpha)\|$ is antitone on
  $(0, \infty)$.
* `Matrix.strictAntiOn_norm_toEuclideanLin_tikhonov`: it is strictly decreasing if $A^H b \ne 0$.
* `Matrix.continuousOn_norm_toEuclideanLin_tikhonov`: it is continuous on $(0, \infty)$.
* `Matrix.tendsto_norm_toEuclideanLin_tikhonov_atTop`: it tends to $0$ as $\alpha \to \infty$.
* `Matrix.tendsto_tikhonov_pinv`: the Tikhonov matrix tends to $A^+$ as $\alpha \to 0^+$.
* `Matrix.isLeastSquaresSolution_fromRows_iff`: a penalized problem is the least-squares problem of
  a stacked matrix, (6.1.11) and (6.1.20) of [golub2013matrix].
* `Matrix.posDef_gram_add_smul_gram_iff`: $A^H A + \alpha B^H B$ is positive definite if and only if
  $\ker A \cap \ker B = 0$.
* `Matrix.eq_toEuclideanLin_generalFormTikhonov_iff`: the general-form solution is characterized by
  its normal equations and as the minimizer, (6.1.20)–(6.1.21) of [golub2013matrix].
* `Matrix.eq_toEuclideanLin_tikhonov_iff_isMinOn`: $x(\alpha)$ is the unique minimizer of
  $\|Ax - b\|^2 + \alpha \|x\|^2$, (6.1.11)–(6.1.12) of [golub2013matrix].
* `Matrix.tikhonov_deleteRow_eq`: the ridge solution with one equation deleted, (6.1.16) of
  [golub2013matrix].
* `Matrix.tikhonov_deleteRow_residual_eq`: the leave-one-out residual, (6.1.17) of
  [golub2013matrix].
* `Matrix.toEuclideanLin_tikhonov_eq_sum_of_isSVD`: $x(\alpha) = \sum_i \sigma_i \langle u_i, b
  \rangle / (\sigma_i^2 + \alpha) \, v_i$, (6.1.14) of [golub2013matrix].
* `Matrix.norm_sq_toEuclideanLin_pinv_eq_sum_of_isSVD`: $\|A^+ b\|^2 = \sum_i (|\langle u_i, b
  \rangle| / \sigma_i)^2$, (6.2.3) of [golub2013matrix].
* `Matrix.norm_sq_toEuclideanLin_tikhonov_sub_eq_sum_of_isSVD`: the ridge residual, (6.2.4) of
  [golub2013matrix].
* `Matrix.norm_sub_sq_pinv_eq_sum_of_isSVD`: the least residual $\|A A^+ b - b\|^2 = \sum_{i >
  \operatorname{rank} A} |\langle u_i, b \rangle|^2$, (5.3.3) of [golub2013matrix].
* `Matrix.generalFormTikhonov_mulVec_eq_sum_of_isGSVD`: the general form in GSVD coordinates,
  (6.1.26) of [golub2013matrix].

## Implementation notes

* The facts that hold for every index type are proved in the right singular basis
  `Matrix.rightSingularBasis` of `Numlib.LinearAlgebra.Matrix.SVD`, in which the resolvent
  $(\alpha I + A^H A)^{-1}$ is diagonal. The statements that name singular vectors $u_i$, $v_i$ take
  a factorization `Matrix.IsSVD A U σ V` on `Fin` indices, not a fixed SVD, because the SVD is not
  unique.
* The cross-validation formulas are stated over $\mathbb{R}$, because they are statistical and use
  $a_k^T x$ without conjugation. Deleting a row is the weight update
  `Matrix.conjTranspose_mul_diagonal_update_mul` of
  `Numlib.LinearAlgebra.Matrix.LeastSquares.Weighted` at weight $0$.
* The GSVD facts that this module and `Numlib.LinearAlgebra.Matrix.LeastSquares.Constrained` use are
  in `Numlib.LinearAlgebra.Matrix.GSVD`: `Matrix.IsGSVD.conjTranspose_mul_conjTranspose_left`,
  `Matrix.IsGSVD.sq_add_smul_sq_ne_zero` and `Matrix.IsGSVD.rank_eq_and_ne_zero`.
* The Lean inverse of a singular matrix is $0$. Hence `Matrix.tikhonov A α` and
  `Matrix.generalFormTikhonov A B α` are $0$ when the matrix to be inverted is singular.
-/

open Module Filter Topology

/-! ### A strictly monotone function between two limits takes every value once -/

/-- Let $f \colon \mathbb{R} \to \mathbb{R}$ be continuous and strictly increasing on $(0, \infty)$,
with $f(t) \to a$ as $t \to 0^+$ and $f(t) \to b$ as $t \to \infty$. Then for every $c$ with
$a < c < b$ there is exactly one $t > 0$ with $f(t) = c$.

Existence is the intermediate value theorem between a point below and a point above $c$, and
uniqueness is injectivity. -/
theorem existsUnique_pos_eq_of_strictMonoOn_Ioi {f : ℝ → ℝ} {a b c : ℝ}
    (hf : StrictMonoOn f (Set.Ioi 0)) (hc : ContinuousOn f (Set.Ioi 0))
    (h0 : Tendsto f (𝓝[>] 0) (𝓝 a)) (htop : Tendsto f atTop (𝓝 b)) (hac : a < c)
    (hcb : c < b) : ∃! t, 0 < t ∧ f t = c := by
  obtain ⟨t₁, ht₁, hft₁⟩ : ∃ t₁, 0 < t₁ ∧ f t₁ < c := by
    obtain ⟨t, ht, ht0⟩ := ((h0.eventually (gt_mem_nhds hac)).and self_mem_nhdsWithin).exists
    exact ⟨t, ht0, ht⟩
  obtain ⟨t₂, ht₂, hft₂⟩ : ∃ t₂, t₁ < t₂ ∧ c < f t₂ := by
    obtain ⟨t, ht, ht1⟩ :=
      ((htop.eventually (lt_mem_nhds hcb)).and (eventually_gt_atTop t₁)).exists
    exact ⟨t, ht1, ht⟩
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc ht₂.le
    (hc.mono fun s hs => lt_of_lt_of_le ht₁ hs.1) ⟨hft₁.le, hft₂.le⟩
  exact ⟨t, ⟨lt_of_lt_of_le ht₁ ht.1, hft⟩, fun s hs =>
    hf.injOn hs.1 (lt_of_lt_of_le ht₁ ht.1) (hs.2.trans hft.symm)⟩

/-- Let $f \colon \mathbb{R} \to \mathbb{R}$ be continuous and strictly decreasing on $(0, \infty)$,
with $f(t) \to a$ as $t \to 0^+$ and $f(t) \to b$ as $t \to \infty$. Then for every $c$ with
$b < c < a$ there is exactly one $t > 0$ with $f(t) = c$.

This is `existsUnique_pos_eq_of_strictMonoOn_Ioi` for $-f$. -/
theorem existsUnique_pos_eq_of_strictAntiOn_Ioi {f : ℝ → ℝ} {a b c : ℝ}
    (hf : StrictAntiOn f (Set.Ioi 0)) (hc : ContinuousOn f (Set.Ioi 0))
    (h0 : Tendsto f (𝓝[>] 0) (𝓝 a)) (htop : Tendsto f atTop (𝓝 b)) (hbc : b < c)
    (hca : c < a) : ∃! t, 0 < t ∧ f t = c := by
  have h := existsUnique_pos_eq_of_strictMonoOn_Ioi (f := fun t => -f t)
    (fun x hx y hy hxy => neg_lt_neg (hf hx hy hxy)) hc.neg h0.neg htop.neg (neg_lt_neg hca)
    (neg_lt_neg hbc)
  simpa only [neg_inj] using h

namespace Matrix

section IndexTypes

variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq n]

/-! ### The regularized normal equations -/

section Identity

variable [DecidableEq m]

/-- Let $A \in \mathbb{K}^{m \times n}$, $B \in \mathbb{K}^{p \times n}$, $b \in \mathbb{K}^m$ and
$\alpha \in \mathbb{R}$, and let $z \in \mathbb{K}^n$ solve the regularized normal equations
$(A^H A + \alpha B^H B) z = A^H b$. Then for every $x \in \mathbb{K}^n$,
$$\|Ax - b\|^2 + \alpha \|Bx\|^2 = \|Az - b\|^2 + \alpha \|Bz\|^2 + \bigl(\|A(x - z)\|^2 +
  \alpha \|B(x - z)\|^2\bigr).$$

The cross term is the real part of $\langle (A^H A + \alpha B^H B) z - A^H b, x - z \rangle =
0$. Every characterization of minimizers in this module follows from this identity. -/
theorem norm_sub_sq_add_mul_norm_sq_eq_of_gram_add_smul_gram (A : Matrix m n 𝕜)
    (B : Matrix p n 𝕜) (α : ℝ) (b : EuclideanSpace 𝕜 m) {z : EuclideanSpace 𝕜 n}
    (hz : toEuclideanLin (Aᴴ * A + (α : 𝕜) • (Bᴴ * B)) z = toEuclideanLin Aᴴ b)
    (x : EuclideanSpace 𝕜 n) :
    ‖toEuclideanLin A x - b‖ ^ 2 + α * ‖toEuclideanLin B x‖ ^ 2
      = ‖toEuclideanLin A z - b‖ ^ 2 + α * ‖toEuclideanLin B z‖ ^ 2
        + (‖toEuclideanLin A (x - z)‖ ^ 2 + α * ‖toEuclideanLin B (x - z)‖ ^ 2) := by
  classical
  set d := x - z with hd
  have hzero : toEuclideanLin Aᴴ (toEuclideanLin A z - b)
      + (α : 𝕜) • toEuclideanLin Bᴴ (toEuclideanLin B z) = 0 := by
    rw [map_sub, ← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply, ← hz, map_add,
      LinearMap.add_apply, map_smul, LinearMap.smul_apply]
    abel
  have hre : RCLike.re (inner 𝕜 (toEuclideanLin A z - b) (toEuclideanLin A d) : 𝕜)
      + α * RCLike.re (inner 𝕜 (toEuclideanLin B z) (toEuclideanLin B d) : 𝕜) = 0 := by
    have h := congrArg (fun w => RCLike.re (inner 𝕜 w d : 𝕜)) hzero
    simp only [inner_add_left, inner_smul_left, RCLike.conj_ofReal, inner_zero_left, map_add,
      RCLike.re_ofReal_mul, map_zero, toEuclideanLin_conjTranspose_inner_left] at h
    exact h
  have hAx : toEuclideanLin A x - b = (toEuclideanLin A z - b) + toEuclideanLin A d := by
    rw [hd, map_sub]; abel
  have hBx : toEuclideanLin B x = toEuclideanLin B z + toEuclideanLin B d := by
    rw [hd, map_sub]; abel
  rw [hAx, hBx, norm_add_sq (𝕜 := 𝕜), norm_add_sq (𝕜 := 𝕜)]
  linear_combination 2 * hre

end Identity

section Kress

variable (A : Matrix m n 𝕜)

/-! ### Tikhonov regularization -/

section Tikhonov

variable (α : ℝ)

/-- Let $A \in \mathbb{K}^{m \times n}$ and $\alpha \in \mathbb{R}$. The **Tikhonov regularization**
of $A$ at level $\alpha$ is the matrix
$$(\alpha I + A^H A)^{-1} A^H \in \mathbb{K}^{n \times m}.$$
Applied to $y$, it gives the regularized solution of $Ax = y$.

For $\alpha > 0$, its value at $y$ is the unique solution of the regularized normal equations
$\alpha x + A^H A x = A^H y$ (`Matrix.tikhonov_unique`) and the unique minimizer of
$x \mapsto \|Ax - y\|^2 + \alpha \|x\|^2$ (`Matrix.eq_toEuclideanLin_tikhonov_iff_isMinOn`). In
the right singular basis it multiplies the $i$-th coordinate by
$\sigma_i / (\alpha + \sigma_i^2)$, which is `Matrix.mul_inv_smul_one_add_gram` read through
`Matrix.exists_singularSystem`. If $\alpha I + A^H A$ is singular, the matrix is $0$. -/
noncomputable def tikhonov (A : Matrix m n 𝕜) (α : ℝ) : Matrix n m 𝕜 :=
  ((α : 𝕜) • 1 + Aᴴ * A)⁻¹ * Aᴴ

/-- For $A \in \mathbb{K}^{m \times n}$ and $\alpha \in \mathbb{R}$, the Tikhonov matrix is
$(\alpha I + A^H A)^{-1} A^H$. This is the definition of `Matrix.tikhonov`. -/
theorem tikhonov_def : A.tikhonov α = ((α : 𝕜) • 1 + Aᴴ * A)⁻¹ * Aᴴ := rfl

/-- Let $A \in \mathbb{K}^{m \times n}$ and $\alpha \in \mathbb{R}$. With the right singular unitary
$W$ of $A$ and the singular values $\sigma_i$,
$$\alpha I + A^H A = W \operatorname{diag}(\alpha + \sigma_i^2) W^H.$$

The singular values are `Matrix.colSingularValues`, and the matrix $W$ is
`Matrix.rightSingularUnitary`. -/
theorem smul_one_add_gram_eq :
    (α : 𝕜) • 1 + Aᴴ * A
      = A.rightSingularUnitary * diagonal (fun i => ((α + A.colSingularValues i ^ 2 : ℝ) : 𝕜))
        * star A.rightSingularUnitary := by
  have hconst : (diagonal fun _ : n => (α : 𝕜)) = (α : 𝕜) • (1 : Matrix n n 𝕜) := by
    ext i j
    rcases eq_or_ne i j with rfl | h
    · simp
    · simp [h]
  have h1 : (α : 𝕜) • (1 : Matrix n n 𝕜)
      = A.rightSingularUnitary * diagonal (fun _ : n => (α : 𝕜))
        * star A.rightSingularUnitary := by
    rw [hconst, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      A.rightSingularUnitary_mul_star]
  rw [h1, conjTranspose_mul_self_eq_conj_diagonal, ← Matrix.add_mul, ← Matrix.mul_add,
    diagonal_add]
  congr 2
  funext i
  push_cast
  ring

/-- Let $A \in \mathbb{K}^{m \times n}$ and $\alpha > 0$. With the right singular unitary $W$ of $A$
and the singular values $\sigma_i$,
$$(\alpha I + A^H A) \, W \operatorname{diag}\bigl((\alpha + \sigma_i^2)^{-1}\bigr) W^H = I.$$
-/
theorem mul_inv_smul_one_add_gram (hα : 0 < α) :
    ((α : 𝕜) • 1 + Aᴴ * A) * (A.rightSingularUnitary *
        diagonal (fun i => ((α + A.colSingularValues i ^ 2 : ℝ) : 𝕜)⁻¹)
        * star A.rightSingularUnitary) = 1 := by
  have hne : ∀ i, ((α + A.colSingularValues i ^ 2 : ℝ) : 𝕜) ≠ 0 := by
    intro i
    have hpos : (0 : ℝ) < α + A.colSingularValues i ^ 2 := by positivity
    rw [Ne, RCLike.ofReal_eq_zero]
    exact hpos.ne'
  rw [smul_one_add_gram_eq, conj_diagonal_mul_conj_diagonal]
  have hone : (fun i => ((α + A.colSingularValues i ^ 2 : ℝ) : 𝕜)
      * ((α + A.colSingularValues i ^ 2 : ℝ) : 𝕜)⁻¹) = fun _ : n => (1 : 𝕜) :=
    funext fun i => mul_inv_cancel₀ (hne i)
  have hdiag : (diagonal fun _ : n => (1 : 𝕜)) = 1 := by
    ext i j
    rcases eq_or_ne i j with rfl | h
    · simp
    · simp [h]
  rw [hone, hdiag, Matrix.mul_one, A.rightSingularUnitary_mul_star]

/-- For $A \in \mathbb{K}^{m \times n}$ and $\alpha > 0$, the matrix $\alpha I + A^H A$ is
nonsingular. -/
theorem isUnit_det_smul_one_add_gram (hα : 0 < α) :
    IsUnit ((α : 𝕜) • 1 + Aᴴ * A).det :=
  Matrix.isUnit_det_of_right_inverse (A.mul_inv_smul_one_add_gram α hα)

/-- The matrix $\alpha I + A^H A$ acts by $x \mapsto \alpha x + A^H A x$. -/
theorem toEuclideanLin_smul_one_add_gram (x : EuclideanSpace 𝕜 n) :
    toEuclideanLin ((α : 𝕜) • 1 + Aᴴ * A) x = (α : 𝕜) • x + toEuclideanLin (Aᴴ * A) x := by
  rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, toLpLin_one,
    LinearMap.id_apply]

variable [DecidableEq m]

/-- Let $A \in \mathbb{K}^{m \times n}$, $\alpha > 0$ and $y \in \mathbb{K}^m$. A vector
$x \in \mathbb{K}^n$ solves the regularized normal equations
$$\alpha x + A^H A x = A^H y$$
if and only if $x = (\alpha I + A^H A)^{-1} A^H y$. This is part of Theorem 5.7 of
[kress1998numerical]. -/
theorem tikhonov_unique (hα : 0 < α) (y : EuclideanSpace 𝕜 m) (x : EuclideanSpace 𝕜 n) :
    (α : 𝕜) • x + toEuclideanLin (Aᴴ * A) x = toEuclideanLin Aᴴ y
      ↔ x = toEuclideanLin (A.tikhonov α) y := by
  have hdet := A.isUnit_det_smul_one_add_gram α hα
  rw [← toEuclideanLin_smul_one_add_gram]
  constructor
  · intro h
    have h2 := congrArg (toEuclideanLin ((α : 𝕜) • 1 + Aᴴ * A)⁻¹) h
    rw [← toEuclideanLin_mul_apply, Matrix.nonsing_inv_mul _ hdet, toLpLin_one,
      LinearMap.id_apply] at h2
    rw [h2, tikhonov_def, toEuclideanLin_mul_apply]
  · intro h
    rw [h, tikhonov_def, ← toEuclideanLin_mul_apply, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]

/-- Let $A \in \mathbb{K}^{m \times n}$, $\alpha \ge 0$ and $y \in \mathbb{K}^m$, and let $z$ solve
the regularized normal equations $\alpha z + A^H A z = A^H y$. Then $z$ minimizes the
regularized least-squares functional: for every $x \in \mathbb{K}^n$,
$$\|Az - y\|^2 + \alpha \|z\|^2 \le \|Ax - y\|^2 + \alpha \|x\|^2.$$
This is part of Theorem 5.7 of [kress1998numerical].

The first-order term of the expansion around $z$ vanishes because $z$ solves the normal
equations, and the remainder $\|A(x - z)\|^2 + \alpha \|x - z\|^2$ is nonnegative. -/
theorem norm_sub_sq_add_mul_norm_sq_le_of_smul_add_gram (hα : 0 ≤ α) (y : EuclideanSpace 𝕜 m)
    {z : EuclideanSpace 𝕜 n} (hz : (α : 𝕜) • z + toEuclideanLin (Aᴴ * A) z = toEuclideanLin Aᴴ y)
    (x : EuclideanSpace 𝕜 n) :
    ‖toEuclideanLin A z - y‖ ^ 2 + α * ‖z‖ ^ 2
      ≤ ‖toEuclideanLin A x - y‖ ^ 2 + α * ‖x‖ ^ 2 := by
  have hz' : toEuclideanLin (Aᴴ * A + (α : 𝕜) • ((1 : Matrix n n 𝕜)ᴴ * 1)) z
      = toEuclideanLin Aᴴ y := by
    rw [conjTranspose_one, Matrix.mul_one, add_comm, toEuclideanLin_smul_one_add_gram, hz]
  have key := norm_sub_sq_add_mul_norm_sq_eq_of_gram_add_smul_gram A 1 α y hz' x
  simp only [toEuclideanLin_one_apply] at key
  rw [key]
  nlinarith [sq_nonneg ‖toEuclideanLin A (x - z)‖, mul_nonneg hα (sq_nonneg ‖x - z‖)]

/-- Let $A \in \mathbb{K}^{m \times n}$, $\alpha > 0$ and $y \in \mathbb{K}^m$. Then
$x(\alpha) = (\alpha I + A^H A)^{-1} A^H y$ minimizes the regularized least-squares functional:
for every $x \in \mathbb{K}^n$,
$$\|Ax(\alpha) - y\|^2 + \alpha \|x(\alpha)\|^2 \le \|Ax - y\|^2 + \alpha \|x\|^2.$$
-/
theorem norm_sub_sq_add_mul_norm_sq_tikhonov_le (hα : 0 < α) (y : EuclideanSpace 𝕜 m)
    (x : EuclideanSpace 𝕜 n) :
    ‖toEuclideanLin A (toEuclideanLin (A.tikhonov α) y) - y‖ ^ 2
        + α * ‖toEuclideanLin (A.tikhonov α) y‖ ^ 2
      ≤ ‖toEuclideanLin A x - y‖ ^ 2 + α * ‖x‖ ^ 2 :=
  A.norm_sub_sq_add_mul_norm_sq_le_of_smul_add_gram α hα.le y
    ((A.tikhonov_unique α hα y _).2 rfl) x

end Tikhonov

/-! ### The discrepancy principle -/

section Discrepancy

/-- Let $A \in \mathbb{K}^{m \times n}$ and $\alpha > 0$. The Tikhonov matrix is a correction of the
pseudoinverse:
$$(\alpha I + A^H A)^{-1} A^H = A^+ - \alpha (\alpha I + A^H A)^{-1} A^+.$$

The identity holds because $A^H y = A^H A A^+ y$ for every $y$. -/
theorem tikhonov_eq_pinv_sub (α : ℝ) (hα : 0 < α) :
    A.tikhonov α = A.pinv - (α : 𝕜) • (((α : 𝕜) • 1 + Aᴴ * A)⁻¹ * A.pinv) := by
  have hdet := A.isUnit_det_smul_one_add_gram α hα
  have h1 : ((α : 𝕜) • 1 + Aᴴ * A)⁻¹ * ((α : 𝕜) • 1 + Aᴴ * A) = 1 :=
    Matrix.nonsing_inv_mul _ hdet
  have hAH : Aᴴ * A * A.pinv = Aᴴ := by rw [Matrix.mul_assoc, conjTranspose_mul_mul_pinv]
  have h2 : (((α : 𝕜) • 1 + Aᴴ * A) - (α : 𝕜) • 1) * A.pinv
      = ((α : 𝕜) • 1 + Aᴴ * A) * A.pinv - (α : 𝕜) • A.pinv := by
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]
  calc A.tikhonov α
      = ((α : 𝕜) • 1 + Aᴴ * A)⁻¹ * (Aᴴ * A * A.pinv) := by rw [hAH, tikhonov_def]
    _ = ((α : 𝕜) • 1 + Aᴴ * A)⁻¹ * ((((α : 𝕜) • 1 + Aᴴ * A) - (α : 𝕜) • 1) * A.pinv) := by
        congr 2
        abel
    _ = A.pinv - (α : 𝕜) • (((α : 𝕜) • 1 + Aᴴ * A)⁻¹ * A.pinv) := by
        rw [h2, Matrix.mul_sub, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_smul]

/-- Let $A \in \mathbb{K}^{m \times n}$ and $\alpha > 0$. Then $A^+ A (\alpha I + A^H A)^{-1} A^H =
(\alpha I + A^H A)^{-1} A^H$: the Tikhonov solutions lie in the range of $A^H$, on which $A^+ A$
is the identity.

The projector $A^+ A$ commutes with $\alpha I + A^H A$, because both are diagonal in the right
singular basis. -/
theorem pinv_mul_self_mul_tikhonov (α : ℝ) (hα : 0 < α) :
    A.pinv * A * A.tikhonov α = A.tikhonov α := by
  have hdet := A.isUnit_det_smul_one_add_gram α hα
  have h1 : A.pinv * A * (Aᴴ * A) = Aᴴ * A := by
    rw [← Matrix.mul_assoc, pinv_mul_self_mul_conjTranspose]
  have h2 : Aᴴ * A * (A.pinv * A) = Aᴴ * A := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc A A.pinv A, mul_pinv_mul_self]
  have hcomm : A.pinv * A * ((α : 𝕜) • 1 + Aᴴ * A)
      = ((α : 𝕜) • 1 + Aᴴ * A) * (A.pinv * A) := by
    rw [Matrix.mul_add, Matrix.add_mul, h1, h2, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul]
  have hinv : A.pinv * A * ((α : 𝕜) • 1 + Aᴴ * A)⁻¹
      = ((α : 𝕜) • 1 + Aᴴ * A)⁻¹ * (A.pinv * A) := by
    calc A.pinv * A * ((α : 𝕜) • 1 + Aᴴ * A)⁻¹
        = (((α : 𝕜) • 1 + Aᴴ * A)⁻¹ * ((α : 𝕜) • 1 + Aᴴ * A)) *
            (A.pinv * A * ((α : 𝕜) • 1 + Aᴴ * A)⁻¹) := by
          rw [Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
      _ = ((α : 𝕜) • 1 + Aᴴ * A)⁻¹ * ((((α : 𝕜) • 1 + Aᴴ * A) * (A.pinv * A)) *
            ((α : 𝕜) • 1 + Aᴴ * A)⁻¹) := by simp only [Matrix.mul_assoc]
      _ = ((α : 𝕜) • 1 + Aᴴ * A)⁻¹ * ((A.pinv * A * ((α : 𝕜) • 1 + Aᴴ * A)) *
            ((α : 𝕜) • 1 + Aᴴ * A)⁻¹) := by rw [hcomm]
      _ = ((α : 𝕜) • 1 + Aᴴ * A)⁻¹ * (A.pinv * A) := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
  rw [tikhonov_def, ← Matrix.mul_assoc, hinv, Matrix.mul_assoc,
    pinv_mul_self_mul_conjTranspose]

/-- Let $A \in \mathbb{K}^{m \times n}$, $\alpha > 0$ and $v \in \mathbb{K}^n$. The resolvent of
$A^H A$ divides the $i$-th coefficient in the right singular basis by $\alpha + \sigma_i^2$:
$$\langle w_i, (\alpha I + A^H A)^{-1} v \rangle = (\alpha + \sigma_i^2)^{-1} \langle w_i, v
  \rangle.$$
-/
theorem inner_rightSingularBasis_inv_smul_one_add_gram (α : ℝ) (hα : 0 < α)
    (v : EuclideanSpace 𝕜 n) (i : n) :
    (inner 𝕜 (A.rightSingularBasis i)
        (toEuclideanLin ((α : 𝕜) • 1 + Aᴴ * A)⁻¹ v) : 𝕜)
      = ((α + A.colSingularValues i ^ 2 : ℝ) : 𝕜)⁻¹ * inner 𝕜 (A.rightSingularBasis i) v := by
  have hdet := A.isUnit_det_smul_one_add_gram α hα
  have hne : ((α + A.colSingularValues i ^ 2 : ℝ) : 𝕜) ≠ 0 := by
    have hpos : (0 : ℝ) < α + A.colSingularValues i ^ 2 := by positivity
    rw [Ne, RCLike.ofReal_eq_zero]
    exact hpos.ne'
  have hmp : (α : 𝕜) • toEuclideanLin ((α : 𝕜) • 1 + Aᴴ * A)⁻¹ v
      + toEuclideanLin (Aᴴ * A) (toEuclideanLin ((α : 𝕜) • 1 + Aᴴ * A)⁻¹ v) = v := by
    rw [← toEuclideanLin_smul_one_add_gram, ← toEuclideanLin_mul_apply,
      Matrix.mul_nonsing_inv _ hdet, toLpLin_one, LinearMap.id_apply]
  have hinner := congrArg (fun x => (inner 𝕜 (A.rightSingularBasis i) x : 𝕜)) hmp
  simp only [inner_add_right, inner_smul_right] at hinner
  rw [← inner_toEuclideanLin_of_isHermitian (isHermitian_conjTranspose_mul_self A),
    toEuclideanLin_conjTranspose_mul_self_rightSingularBasis, inner_smul_left,
    RCLike.conj_ofReal] at hinner
  have h2 : ((α + A.colSingularValues i ^ 2 : ℝ) : 𝕜) *
      (inner 𝕜 (A.rightSingularBasis i)
        (toEuclideanLin ((α : 𝕜) • 1 + Aᴴ * A)⁻¹ v) : 𝕜)
      = inner 𝕜 (A.rightSingularBasis i) v := by
    push_cast at hinner ⊢
    linear_combination hinner
  rw [← h2, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-- Let $A \in \mathbb{K}^{m \times n}$, $\alpha > 0$ and $v \in \mathbb{K}^n$. Then
$$\|A (\alpha I + A^H A)^{-1} v\|^2 = \sum_i \Bigl(\frac{\sigma_i}{\alpha + \sigma_i^2}\Bigr)^2
  |\langle w_i, v \rangle|^2.$$
-/
theorem norm_sq_toEuclideanLin_inv_smul_one_add_gram (α : ℝ) (hα : 0 < α)
    (v : EuclideanSpace 𝕜 n) :
    ‖toEuclideanLin A (toEuclideanLin ((α : 𝕜) • 1 + Aᴴ * A)⁻¹ v)‖ ^ 2
      = ∑ i, (A.colSingularValues i / (α + A.colSingularValues i ^ 2)) ^ 2 *
          ‖(inner 𝕜 (A.rightSingularBasis i) v : 𝕜)‖ ^ 2 := by
  rw [norm_sq_toEuclideanLin_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hpos : (0 : ℝ) < α + A.colSingularValues i ^ 2 := by positivity
  have hne : α + A.colSingularValues i ^ 2 ≠ 0 := hpos.ne'
  rw [A.inner_rightSingularBasis_inv_smul_one_add_gram α hα v i, norm_mul, norm_inv,
    RCLike.norm_ofReal, abs_of_pos hpos]
  field_simp

variable [DecidableEq m]

/-- Let $A \in \mathbb{K}^{m \times n}$, $\alpha > 0$ and $y^\delta \in \mathbb{K}^m$, and let
$w = A^+ y^\delta$ and $x(\alpha) = (\alpha I + A^H A)^{-1} A^H y^\delta$. Then the squared norm
of the Tikhonov residual is
$$\|A x(\alpha) - y^\delta\|^2 = \|A w - y^\delta\|^2 + \sum_i \Bigl(\frac{\alpha
  \sigma_i}{\alpha + \sigma_i^2}\Bigr)^2 |\langle w_i, w \rangle|^2.$$

The residual splits orthogonally into the least-squares residual $Aw - y^\delta$, which does not
depend on $\alpha$, and a correction in the range of $A$. -/
theorem norm_sq_toEuclideanLin_tikhonov_sub (α : ℝ) (hα : 0 < α) (yδ : EuclideanSpace 𝕜 m) :
    ‖toEuclideanLin A (toEuclideanLin (A.tikhonov α) yδ) - yδ‖ ^ 2
      = ‖toEuclideanLin A (toEuclideanLin A.pinv yδ) - yδ‖ ^ 2
        + ∑ i, (α * A.colSingularValues i / (α + A.colSingularValues i ^ 2)) ^ 2 *
            ‖(inner 𝕜 (A.rightSingularBasis i) (toEuclideanLin A.pinv yδ) : 𝕜)‖ ^ 2 := by
  have hres : toEuclideanLin A (toEuclideanLin (A.tikhonov α) yδ) - yδ
      = (toEuclideanLin A (toEuclideanLin A.pinv yδ) - yδ)
        - (α : 𝕜) • toEuclideanLin A
            (toEuclideanLin ((α : 𝕜) • 1 + Aᴴ * A)⁻¹ (toEuclideanLin A.pinv yδ)) := by
    rw [tikhonov_eq_pinv_sub A α hα]
    simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply,
      toEuclideanLin_mul_apply]
    abel
  have hperp : (inner 𝕜 (toEuclideanLin A (toEuclideanLin A.pinv yδ) - yδ)
      ((α : 𝕜) • toEuclideanLin A
        (toEuclideanLin ((α : 𝕜) • 1 + Aᴴ * A)⁻¹ (toEuclideanLin A.pinv yδ))) : 𝕜) = 0 := by
    rw [inner_smul_right, ← inner_conj_symm, A.inner_toEuclideanLin_sub_pinv yδ _, map_zero,
      mul_zero]
  rw [hres, norm_sub_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := 𝕜) _ _ hperp, norm_smul,
    mul_pow, RCLike.norm_ofReal, abs_of_pos hα,
    A.norm_sq_toEuclideanLin_inv_smul_one_add_gram α hα, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The **discrepancy principle** for Tikhonov regularization. Let $A \in \mathbb{K}^{m \times n}$,
$y^\delta \in \mathbb{K}^m$ and $\delta \in \mathbb{R}$ with
$$\inf_{x} \|Ax - y^\delta\| < \delta < \|y^\delta\|.$$
Then there is exactly one $\alpha > 0$ such that the Tikhonov solution $x(\alpha) = (\alpha I +
A^H A)^{-1} A^H y^\delta$ satisfies $\|A x(\alpha) - y^\delta\| = \delta$. This is the existence
part of Theorem 5.10 of [kress1998numerical].

The two hypotheses are sharp: the residual norm increases strictly from
$\inf_x \|Ax - y^\delta\|$ at $\alpha = 0$ to $\|y^\delta\|$ as $\alpha \to \infty$. The source
states the lower hypothesis as $\|y^\delta - y\| \le \delta$ for some $y$ in the range of $A$.
This gives only $\inf_x \|Ax - y^\delta\| \le \delta$, and with equality no such $\alpha$
exists, as $A = \operatorname{diag}(1, 0)$, $y = (1, 0)$, $y^\delta = (1, \delta)$ shows. -/
theorem exists_discrepancy_tikhonov (yδ : EuclideanSpace 𝕜 m) {δ : ℝ}
    (hlow : ⨅ x : EuclideanSpace 𝕜 n, ‖toEuclideanLin A x - yδ‖ < δ) (hhigh : δ < ‖yδ‖) :
    ∃! α : ℝ, 0 < α ∧
      ‖toEuclideanLin A (toEuclideanLin (A.tikhonov α) yδ) - yδ‖ = δ := by
  classical
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, F = fun t =>
      ‖toEuclideanLin A (toEuclideanLin A.pinv yδ) - yδ‖ ^ 2
        + ∑ i, (t * A.colSingularValues i / (t + A.colSingularValues i ^ 2)) ^ 2 *
            ‖(inner 𝕜 (A.rightSingularBasis i) (toEuclideanLin A.pinv yδ) : 𝕜)‖ ^ 2 := ⟨_, rfl⟩
  have hd : ‖toEuclideanLin A (toEuclideanLin A.pinv yδ) - yδ‖ < δ := by
    rw [A.norm_toEuclideanLin_pinv_sub_eq_iInf yδ]; exact hlow
  have hδ0 : 0 < δ := lt_of_le_of_lt (norm_nonneg _) hd
  have hsplit : ‖yδ‖ ^ 2 = ‖toEuclideanLin A (toEuclideanLin A.pinv yδ)‖ ^ 2
      + ‖toEuclideanLin A (toEuclideanLin A.pinv yδ) - yδ‖ ^ 2 := by
    have key := norm_sub_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := 𝕜)
      (toEuclideanLin A (toEuclideanLin A.pinv yδ))
      (toEuclideanLin A (toEuclideanLin A.pinv yδ) - yδ)
      (A.inner_toEuclideanLin_sub_pinv yδ _)
    rwa [sub_sub_cancel] at key
  have hAw : 0 < ‖toEuclideanLin A (toEuclideanLin A.pinv yδ)‖ ^ 2 := by
    nlinarith [norm_nonneg (toEuclideanLin A (toEuclideanLin A.pinv yδ) - yδ), hd, hδ0, hhigh,
      hsplit]
  have hParseval : ∑ i, A.colSingularValues i ^ 2 *
      ‖(inner 𝕜 (A.rightSingularBasis i) (toEuclideanLin A.pinv yδ) : 𝕜)‖ ^ 2
      = ‖toEuclideanLin A (toEuclideanLin A.pinv yδ)‖ ^ 2 :=
    (A.norm_sq_toEuclideanLin_apply _).symm
  obtain ⟨i₀, -, hi₀⟩ : ∃ i₀ ∈ (Finset.univ : Finset n), (0 : ℝ) < A.colSingularValues i₀ ^ 2 *
      ‖(inner 𝕜 (A.rightSingularBasis i₀) (toEuclideanLin A.pinv yδ) : 𝕜)‖ ^ 2 := by
    refine Finset.exists_lt_of_sum_lt (f := fun _ => (0 : ℝ)) ?_
    rw [Finset.sum_const_zero, hParseval]
    exact hAw
  have hσ₀ : 0 < A.colSingularValues i₀ := by
    rcases (A.colSingularValues_nonneg i₀).lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hi₀; simp at hi₀
  have hc₀ : 0 < ‖(inner 𝕜 (A.rightSingularBasis i₀) (toEuclideanLin A.pinv yδ) : 𝕜)‖ ^ 2 := by
    nlinarith [hi₀, sq_nonneg (A.colSingularValues i₀)]
  have hFeq : ∀ t : ℝ, 0 < t →
      ‖toEuclideanLin A (toEuclideanLin (A.tikhonov t) yδ) - yδ‖ ^ 2 = F t := by
    intro t ht
    rw [hF]
    exact A.norm_sq_toEuclideanLin_tikhonov_sub t ht yδ
  have hF0 : F 0 = ‖toEuclideanLin A (toEuclideanLin A.pinv yδ) - yδ‖ ^ 2 := by
    rw [hF]; simp
  have hmono : StrictMonoOn F (Set.Ici (0 : ℝ)) := by
    intro s hs t ht hst
    simp only [Set.mem_Ici] at hs ht
    have h1 : ∀ i ∈ (Finset.univ : Finset n),
        (s * A.colSingularValues i / (s + A.colSingularValues i ^ 2)) ^ 2 *
            ‖(inner 𝕜 (A.rightSingularBasis i) (toEuclideanLin A.pinv yδ) : 𝕜)‖ ^ 2
          ≤ (t * A.colSingularValues i / (t + A.colSingularValues i ^ 2)) ^ 2 *
            ‖(inner 𝕜 (A.rightSingularBasis i) (toEuclideanLin A.pinv yδ) : 𝕜)‖ ^ 2 := by
      intro i _
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      rcases (A.colSingularValues_nonneg i).lt_or_eq with hσ | hσ
      · have hs' : (0 : ℝ) < s + A.colSingularValues i ^ 2 := by positivity
        have ht' : (0 : ℝ) < t + A.colSingularValues i ^ 2 := by positivity
        refine pow_le_pow_left₀ (by positivity) ?_ 2
        rw [div_le_div_iff₀ hs' ht']
        have hcube : s * (A.colSingularValues i * A.colSingularValues i * A.colSingularValues i)
            ≤ t * (A.colSingularValues i * A.colSingularValues i * A.colSingularValues i) :=
          mul_le_mul_of_nonneg_right hst.le (by positivity)
        nlinarith [hcube]
      · rw [← hσ]; simp
    have h2 : (s * A.colSingularValues i₀ / (s + A.colSingularValues i₀ ^ 2)) ^ 2 *
          ‖(inner 𝕜 (A.rightSingularBasis i₀) (toEuclideanLin A.pinv yδ) : 𝕜)‖ ^ 2
        < (t * A.colSingularValues i₀ / (t + A.colSingularValues i₀ ^ 2)) ^ 2 *
          ‖(inner 𝕜 (A.rightSingularBasis i₀) (toEuclideanLin A.pinv yδ) : 𝕜)‖ ^ 2 := by
      refine mul_lt_mul_of_pos_right ?_ hc₀
      have hs' : (0 : ℝ) < s + A.colSingularValues i₀ ^ 2 := by positivity
      have ht' : (0 : ℝ) < t + A.colSingularValues i₀ ^ 2 := by positivity
      have hnn : (0 : ℝ) ≤ s * A.colSingularValues i₀ / (s + A.colSingularValues i₀ ^ 2) := by
        positivity
      refine pow_lt_pow_left₀ ?_ hnn two_ne_zero
      rw [div_lt_div_iff₀ hs' ht']
      have hcube : s * (A.colSingularValues i₀ * A.colSingularValues i₀ * A.colSingularValues i₀)
          < t * (A.colSingularValues i₀ * A.colSingularValues i₀ * A.colSingularValues i₀) :=
        mul_lt_mul_of_pos_right hst (by positivity)
      nlinarith [hcube]
    have key := Finset.sum_lt_sum h1 ⟨i₀, Finset.mem_univ _, h2⟩
    simp only [hF]
    linarith
  have hcont : ContinuousOn F (Set.Ici (0 : ℝ)) := by
    rw [hF]
    refine continuousOn_const.add (continuousOn_finsetSum _ fun i _ => ?_)
    rcases eq_or_ne (A.colSingularValues i) 0 with hσ | hσ
    · have hzero : (fun t : ℝ => (t * A.colSingularValues i / (t + A.colSingularValues i ^ 2)) ^ 2 *
          ‖(inner 𝕜 (A.rightSingularBasis i) (toEuclideanLin A.pinv yδ) : 𝕜)‖ ^ 2)
          = fun _ : ℝ => 0 := by
        funext t; simp [hσ]
      rw [hzero]
      exact continuousOn_const
    · have hne : ∀ t ∈ Set.Ici (0 : ℝ), t + A.colSingularValues i ^ 2 ≠ 0 := by
        intro t ht
        simp only [Set.mem_Ici] at ht
        positivity
      exact (((continuousOn_id.mul continuousOn_const).div
        (continuousOn_id.add continuousOn_const) hne).pow 2).mul continuousOn_const
  have hlim : Filter.Tendsto F Filter.atTop (nhds (‖yδ‖ ^ 2)) := by
    have hterm : ∀ i : n, Filter.Tendsto
        (fun t : ℝ => t * A.colSingularValues i / (t + A.colSingularValues i ^ 2)) Filter.atTop
        (nhds (A.colSingularValues i)) := by
      intro i
      have h0 : Filter.Tendsto (fun t : ℝ => A.colSingularValues i ^ 2 /
          (t + A.colSingularValues i ^ 2)) Filter.atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop
          (Filter.tendsto_atTop_add_const_right _ _ Filter.tendsto_id)
      have h1 : Filter.Tendsto (fun t : ℝ => A.colSingularValues i *
          (1 - A.colSingularValues i ^ 2 / (t + A.colSingularValues i ^ 2))) Filter.atTop
          (nhds (A.colSingularValues i * (1 - 0))) :=
        tendsto_const_nhds.mul (tendsto_const_nhds.sub h0)
      rw [sub_zero, mul_one] at h1
      refine h1.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
      have hne : t + A.colSingularValues i ^ 2 ≠ 0 := by positivity
      field_simp
      ring
    have hsum : Filter.Tendsto (fun t : ℝ => ∑ i,
        (t * A.colSingularValues i / (t + A.colSingularValues i ^ 2)) ^ 2 *
          ‖(inner 𝕜 (A.rightSingularBasis i) (toEuclideanLin A.pinv yδ) : 𝕜)‖ ^ 2)
        Filter.atTop (nhds (∑ i, A.colSingularValues i ^ 2 *
          ‖(inner 𝕜 (A.rightSingularBasis i) (toEuclideanLin A.pinv yδ) : 𝕜)‖ ^ 2)) :=
      tendsto_finsetSum _ fun i _ => ((hterm i).pow 2).mul_const _
    rw [hF, hsplit]
    have hadd := (tendsto_const_nhds (α := ℝ) (f := Filter.atTop (α := ℝ))
      (x := ‖toEuclideanLin A (toEuclideanLin A.pinv yδ) - yδ‖ ^ 2)).add hsum
    rw [hParseval] at hadd
    simpa [add_comm] using hadd
  have hF0lt : F 0 < δ ^ 2 := by
    rw [hF0]
    nlinarith [hd, norm_nonneg (toEuclideanLin A (toEuclideanLin A.pinv yδ) - yδ), hδ0]
  have hδ2 : δ ^ 2 < ‖yδ‖ ^ 2 := by nlinarith [hδ0, hhigh]
  have h0 : Tendsto F (𝓝[>] 0) (𝓝 (F 0)) :=
    ((hcont 0 (Set.mem_Ici.2 le_rfl)).mono Set.Ioi_subset_Ici_self).tendsto
  obtain ⟨a, ⟨ha0, hFa⟩, huniq⟩ := existsUnique_pos_eq_of_strictMonoOn_Ioi
    (hmono.mono Set.Ioi_subset_Ici_self) (hcont.mono Set.Ioi_subset_Ici_self) h0 hlim hF0lt hδ2
  have hres : ‖toEuclideanLin A (toEuclideanLin (A.tikhonov a) yδ) - yδ‖ = δ := by
    have h := hFeq a ha0
    rw [hFa] at h
    exact (pow_left_inj₀ (norm_nonneg _) hδ0.le two_ne_zero).1 h
  exact ⟨a, ⟨ha0, hres⟩, fun b hb => huniq b ⟨hb.1, by rw [← hFeq b hb.1, hb.2]⟩⟩

/-- The discrepancy principle is **regular**. Let $A \in \mathbb{K}^{m \times n}$ and let $y$ lie in
the range of $A$. Let $(y^\delta_i)$, $(\delta_i)$ and $(\alpha_i)$ be families indexed by $i$
along a filter, with $\alpha_i > 0$, $\|y^\delta_i - y\| \le \delta_i$, and with $\alpha_i$
chosen by the discrepancy principle: $\|A x_i - y^\delta_i\| = \delta_i$ for
$x_i = (\alpha_i I + A^H A)^{-1} A^H y^\delta_i$. If $\delta_i \to 0$, then
$$x_i \to A^+ y.$$
This is the convergence part of Theorem 5.10 of [kress1998numerical].

No estimate on $\alpha_i$ is needed. The discrepancy condition alone forces the residual to $0$,
and $A^+ A$ is the identity on the range of $A^H$, which contains all Tikhonov solutions. -/
theorem tendsto_tikhonov_of_norm_toEuclideanLin_sub_eq {ι : Type*} {l : Filter ι}
    {y : EuclideanSpace 𝕜 m} (hy : y ∈ LinearMap.range (toEuclideanLin A))
    {yδ : ι → EuclideanSpace 𝕜 m} {δ α : ι → ℝ} (hα : ∀ i, 0 < α i)
    (hyδ : ∀ i, ‖yδ i - y‖ ≤ δ i)
    (hres : ∀ i, ‖toEuclideanLin A (toEuclideanLin (A.tikhonov (α i)) (yδ i)) - yδ i‖ = δ i)
    (hδ : Filter.Tendsto δ l (nhds 0)) :
    Filter.Tendsto (fun i => toEuclideanLin (A.tikhonov (α i)) (yδ i)) l
      (nhds (toEuclideanLin A.pinv y)) := by
  obtain ⟨x₀, rfl⟩ := hy
  have hAp : toEuclideanLin A (toEuclideanLin A.pinv (toEuclideanLin A x₀))
      = toEuclideanLin A x₀ := by
    rw [← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply, Matrix.mul_assoc,
      ← Matrix.mul_assoc A, mul_pinv_mul_self]
  have himg : Filter.Tendsto (fun i => toEuclideanLin A
      (toEuclideanLin (A.tikhonov (α i)) (yδ i) - toEuclideanLin A.pinv (toEuclideanLin A x₀)))
      l (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hbound : ∀ i, ‖toEuclideanLin A (toEuclideanLin (A.tikhonov (α i)) (yδ i)
        - toEuclideanLin A.pinv (toEuclideanLin A x₀))‖ ≤ 2 * δ i := by
      intro i
      rw [map_sub, hAp]
      calc ‖toEuclideanLin A (toEuclideanLin (A.tikhonov (α i)) (yδ i)) - toEuclideanLin A x₀‖
          ≤ ‖toEuclideanLin A (toEuclideanLin (A.tikhonov (α i)) (yδ i)) - yδ i‖
            + ‖yδ i - toEuclideanLin A x₀‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ δ i + δ i := add_le_add (hres i).le (hyδ i)
        _ = 2 * δ i := by ring
    refine squeeze_zero (fun i => norm_nonneg _) hbound ?_
    simpa using hδ.const_mul 2
  have hfix : ∀ i, toEuclideanLin A.pinv (toEuclideanLin A
      (toEuclideanLin (A.tikhonov (α i)) (yδ i)
        - toEuclideanLin A.pinv (toEuclideanLin A x₀)))
      = toEuclideanLin (A.tikhonov (α i)) (yδ i)
        - toEuclideanLin A.pinv (toEuclideanLin A x₀) := by
    intro i
    rw [map_sub, map_sub, ← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply,
      ← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply,
      pinv_mul_self_mul_tikhonov A (α i) (hα i), pinv_mul_self_mul_pinv]
  have hcontp : Continuous
      (toEuclideanLin A.pinv : EuclideanSpace 𝕜 m →ₗ[𝕜] EuclideanSpace 𝕜 n) :=
    LinearMap.continuous_of_finiteDimensional _
  have hdiff : Filter.Tendsto (fun i => toEuclideanLin (A.tikhonov (α i)) (yδ i)
      - toEuclideanLin A.pinv (toEuclideanLin A x₀)) l (nhds 0) := by
    have hcomp := (hcontp.tendsto 0).comp himg
    simp only [Function.comp_def, map_zero] at hcomp
    exact hcomp.congr fun i => hfix i
  have hfinal := hdiff.add (tendsto_const_nhds
    (x := toEuclideanLin A.pinv (toEuclideanLin A x₀)) (f := l))
  simpa using hfinal

end Discrepancy

end Kress

/-! ### The norm of the ridge solution -/

section Spectral

variable [DecidableEq m]

/-- Let $A \in \mathbb{K}^{m \times n}$, $\alpha > 0$ and $b \in \mathbb{K}^m$. In the right
singular basis,
$$\|(\alpha I + A^H A)^{-1} A^H b\|^2 = \sum_i \frac{|\langle w_i, A^H b \rangle|^2}{(\alpha +
  \sigma_i^2)^2}.$$
-/
theorem norm_sq_toEuclideanLin_tikhonov_apply (A : Matrix m n 𝕜) {α : ℝ} (hα : 0 < α)
    (b : EuclideanSpace 𝕜 m) :
    ‖toEuclideanLin (A.tikhonov α) b‖ ^ 2
      = ∑ i, ‖(inner 𝕜 (A.rightSingularBasis i) (toEuclideanLin Aᴴ b) : 𝕜)‖ ^ 2
          / (α + A.colSingularValues i ^ 2) ^ 2 := by
  rw [← A.sum_norm_inner_rightSingularBasis_sq, tikhonov_def, toEuclideanLin_mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hpos : (0 : ℝ) < α + A.colSingularValues i ^ 2 := by positivity
  rw [A.inner_rightSingularBasis_inv_smul_one_add_gram α hα, norm_mul, norm_inv,
    RCLike.norm_ofReal, abs_of_pos hpos, mul_pow, inv_pow, inv_mul_eq_div]

/-- Let $A \in \mathbb{K}^{m \times n}$ and $b \in \mathbb{K}^m$. The norm $\|x(\alpha)\|$ of the
ridge solution $x(\alpha) = (\alpha I + A^H A)^{-1} A^H b$ is antitone in $\alpha$ on
$(0, \infty)$. This is stated in §6.1.4 of [golub2013matrix].

Each term of `Matrix.norm_sq_toEuclideanLin_tikhonov_apply` is antitone. -/
theorem antitoneOn_norm_toEuclideanLin_tikhonov (A : Matrix m n 𝕜) (b : EuclideanSpace 𝕜 m) :
    AntitoneOn (fun α : ℝ => ‖toEuclideanLin (A.tikhonov α) b‖) (Set.Ioi 0) := by
  intro α hα β hβ hαβ
  simp only [Set.mem_Ioi] at hα hβ
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [norm_sq_toEuclideanLin_tikhonov_apply A hα, norm_sq_toEuclideanLin_tikhonov_apply A hβ]
  refine Finset.sum_le_sum fun i _ => div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) ?_
  exact pow_le_pow_left₀ (by positivity) (by linarith) 2

/-- Let $A \in \mathbb{K}^{m \times n}$ and $b \in \mathbb{K}^m$ with $A^H b \ne 0$. Then
$\|x(\alpha)\|$ is strictly decreasing in $\alpha$ on $(0, \infty)$. This is the statement
$f'(\lambda) < 0$ of §6.2.1 of [golub2013matrix].

Some coefficient $\langle w_i, A^H b \rangle$ is nonzero, and its term decreases strictly. -/
theorem strictAntiOn_norm_toEuclideanLin_tikhonov (A : Matrix m n 𝕜) {b : EuclideanSpace 𝕜 m}
    (hb : toEuclideanLin Aᴴ b ≠ 0) :
    StrictAntiOn (fun α : ℝ => ‖toEuclideanLin (A.tikhonov α) b‖) (Set.Ioi 0) := by
  intro α hα β hβ hαβ
  simp only [Set.mem_Ioi] at hα hβ
  have hsum : 0 < ∑ i, ‖(inner 𝕜 (A.rightSingularBasis i) (toEuclideanLin Aᴴ b) : 𝕜)‖ ^ 2 := by
    rw [A.sum_norm_inner_rightSingularBasis_sq]
    exact pow_pos (norm_pos_iff.2 hb) 2
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ) (f := fun _ => (0 : ℝ))
    (g := fun i => ‖(inner 𝕜 (A.rightSingularBasis i) (toEuclideanLin Aᴴ b) : 𝕜)‖ ^ 2)
    (by simpa using hsum)
  refine (pow_lt_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [norm_sq_toEuclideanLin_tikhonov_apply A hα, norm_sq_toEuclideanLin_tikhonov_apply A hβ]
  refine Finset.sum_lt_sum (fun i _ => div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    (pow_le_pow_left₀ (by positivity) (by linarith) 2)) ⟨i₀, Finset.mem_univ _, ?_⟩
  exact div_lt_div_of_pos_left hi₀ (by positivity)
    (pow_lt_pow_left₀ (by linarith) (by positivity) two_ne_zero)

/-- Let $A \in \mathbb{K}^{m \times n}$ and $b \in \mathbb{K}^m$. The norm $\|x(\alpha)\|$ of the
ridge solution is continuous in $\alpha$ on $(0, \infty)$.

Its square is a finite sum of continuous terms (`Matrix.norm_sq_toEuclideanLin_tikhonov_apply`). -/
theorem continuousOn_norm_toEuclideanLin_tikhonov (A : Matrix m n 𝕜) (b : EuclideanSpace 𝕜 m) :
    ContinuousOn (fun α : ℝ => ‖toEuclideanLin (A.tikhonov α) b‖) (Set.Ioi 0) := by
  have hsq : ContinuousOn (fun α : ℝ => ∑ i,
      ‖(inner 𝕜 (A.rightSingularBasis i) (toEuclideanLin Aᴴ b) : 𝕜)‖ ^ 2
        / (α + A.colSingularValues i ^ 2) ^ 2) (Set.Ioi 0) := by
    refine continuousOn_finsetSum _ fun i _ => ?_
    refine continuousOn_const.div ((continuousOn_id.add continuousOn_const).pow 2) fun α hα => ?_
    have : (0 : ℝ) < α := hα
    positivity
  refine (Real.continuous_sqrt.comp_continuousOn hsq).congr fun α hα => ?_
  have : (0 : ℝ) < α := hα
  simp only [Function.comp_apply]
  rw [← norm_sq_toEuclideanLin_tikhonov_apply A this, Real.sqrt_sq (norm_nonneg _)]

/-- Let $A \in \mathbb{K}^{m \times n}$ and $b \in \mathbb{K}^m$. The ridge solution vanishes at
infinity: $\|x(\alpha)\| \to 0$ as $\alpha \to \infty$. This is stated in §6.2.1 of
[golub2013matrix].

Each term of `Matrix.norm_sq_toEuclideanLin_tikhonov_apply` has a denominator that tends to
$\infty$. -/
theorem tendsto_norm_toEuclideanLin_tikhonov_atTop (A : Matrix m n 𝕜) (b : EuclideanSpace 𝕜 m) :
    Tendsto (fun α : ℝ => ‖toEuclideanLin (A.tikhonov α) b‖) atTop (𝓝 0) := by
  have hsq : Tendsto (fun α : ℝ => ∑ i,
      ‖(inner 𝕜 (A.rightSingularBasis i) (toEuclideanLin Aᴴ b) : 𝕜)‖ ^ 2
        / (α + A.colSingularValues i ^ 2) ^ 2) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset n) fun i _ =>
      (tendsto_const_nhds (x := ‖(inner 𝕜 (A.rightSingularBasis i)
        (toEuclideanLin Aᴴ b) : 𝕜)‖ ^ 2)).div_atTop ((tendsto_pow_atTop two_ne_zero).comp
          (tendsto_atTop_add_const_right _ (A.colSingularValues i ^ 2) tendsto_id))
    simpa [Function.comp_def] using this
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
  rw [Function.comp_def, Real.sqrt_zero] at hsqrt
  refine hsqrt.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with α hα
  rw [← norm_sq_toEuclideanLin_tikhonov_apply A hα, Real.sqrt_sq (norm_nonneg _)]

omit [DecidableEq m] in
/-- Let $A \in \mathbb{K}^{m \times n}$. The Tikhonov matrix tends to the pseudoinverse:
$$(\alpha I + A^H A)^{-1} A^H \to A^+ \quad \text{as } \alpha \to 0^+.$$
Hence ridge regression tends to the least-squares solution of least norm,
$\lim_{\lambda \to 0} x(\lambda) = x_{LS}$ in §6.1.4 of [golub2013matrix].

By `Matrix.tikhonov_eq_pinv_sub`, the difference is $\alpha (\alpha I + A^H A)^{-1} A^+ = W
\Delta_\alpha W^H A^H$, where $W$ is the right singular unitary `Matrix.rightSingularUnitary`
and $\Delta_\alpha$ is diagonal with entries $\alpha / ((\alpha + \sigma_i^2) \sigma_i^2)$.
These entries are $0$ when $\sigma_i = 0$, and they are continuous with value $0$ at
$\alpha = 0$. -/
theorem tendsto_tikhonov_pinv (A : Matrix m n 𝕜) :
    Tendsto A.tikhonov (𝓝[>] 0) (𝓝 A.pinv) := by
  set W := A.rightSingularUnitary with hW
  set s : n → ℝ := fun i => A.colSingularValues i ^ 2 with hs
  set k : ℝ → n → 𝕜 := fun α i => ((α * ((α + s i)⁻¹ * (s i)⁻¹) : ℝ) : 𝕜) with hk
  have hinv : ∀ α : ℝ, 0 < α → ((α : 𝕜) • 1 + Aᴴ * A)⁻¹
      = W * diagonal (fun i => ((α + s i : ℝ) : 𝕜)⁻¹) * star W := fun α hα =>
    inv_eq_right_inv (A.mul_inv_smul_one_add_gram α hα)
  have hform : ∀ α : ℝ, 0 < α →
      A.tikhonov α = A.pinv - W * diagonal (k α) * star W * Aᴴ := by
    intro α hα
    rw [tikhonov_eq_pinv_sub A α hα, hinv α hα, pinv_def, gramPinv_def]
    congr 1
    have hWW : star W * W = 1 := A.star_mul_rightSingularUnitary
    have hdiag : diagonal (k α) = (α : 𝕜) • (diagonal (fun i => ((α + s i : ℝ) : 𝕜)⁻¹) *
        diagonal (fun i => ((A.colSingularValues i ^ 2 : ℝ) : 𝕜)⁻¹)) := by
      rw [diagonal_mul_diagonal, ← diagonal_smul]
      congr 1
      funext i
      simp only [hk, hs, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [hdiag]
    simp only [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star W) W, hWW, Matrix.one_mul]
  have hcont : Continuous fun d : n → 𝕜 => A.pinv - W * diagonal d * star W * Aᴴ :=
    continuous_const.sub (((continuous_const.matrix_mul
      (continuous_id.matrix_diagonal)).matrix_mul continuous_const).matrix_mul continuous_const)
  have hk0 : Tendsto k (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_pi_nhds]
    intro i
    by_cases hsi : s i = 0
    · have : (fun α => k α i) = fun _ => 0 := by
        funext α; simp [hk, hsi]
      rw [this]
      exact tendsto_const_nhds
    · have hc : ContinuousAt (fun α : ℝ => ((α * ((α + s i)⁻¹ * (s i)⁻¹) : ℝ) : 𝕜)) 0 := by
        refine RCLike.continuous_ofReal.continuousAt.comp ?_
        refine continuousAt_id.mul (ContinuousAt.mul ?_ continuousAt_const)
        exact (continuousAt_id.add continuousAt_const).inv₀
          (by change (0 : ℝ) + s i ≠ 0; rw [zero_add]; exact hsi)
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      simpa [hk] using this
  have hlim := (hcont.tendsto 0).comp hk0
  have h0 : A.pinv - W * diagonal (0 : n → 𝕜) * star W * Aᴴ = A.pinv := by
    rw [show (0 : n → 𝕜) = fun _ => 0 from rfl, diagonal_zero]
    simp
  rw [h0] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with α hα
  exact (hform α hα).symm

end Spectral

/-! ### Stacked problems -/

section Stacking

/-- Let $A \in \mathbb{K}^{m_1 \times n}$, $B \in \mathbb{K}^{m_2 \times n}$,
$b \in \mathbb{K}^{m_1}$ and $d \in \mathbb{K}^{m_2}$. Then for every $x \in \mathbb{K}^n$,
$$\Bigl\| \begin{bmatrix} A \\ B \end{bmatrix} x - \begin{bmatrix} b \\ d \end{bmatrix}
  \Bigr\|^2 = \|Ax - b\|^2 + \|Bx - d\|^2.$$
This is how [golub2013matrix] (6.1.11), (6.1.20) and (6.2.13) stack least-squares problems. -/
theorem norm_fromRows_sub_sq {m₁ m₂ : Type*} [Fintype m₁] [Fintype m₂] (A : Matrix m₁ n 𝕜)
    (B : Matrix m₂ n 𝕜) (b : m₁ → 𝕜) (d : m₂ → 𝕜) (x : EuclideanSpace 𝕜 n) :
    ‖toEuclideanLin (fromRows A B) x - WithLp.toLp 2 (Sum.elim b d)‖ ^ 2
      = ‖toEuclideanLin A x - WithLp.toLp 2 b‖ ^ 2
        + ‖toEuclideanLin B x - WithLp.toLp 2 d‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type, toEuclideanLin_apply,
    PiLp.sub_apply, fromRows_mulVec, Sum.elim_inl, Sum.elim_inr]

/-- Let $A \in \mathbb{K}^{m_1 \times n}$, $B \in \mathbb{K}^{m_2 \times n}$,
$b \in \mathbb{K}^{m_1}$, $d \in \mathbb{K}^{m_2}$ and $\alpha \ge 0$. Then $x$ is a
least-squares solution of
$$\begin{bmatrix} A \\ \sqrt{\alpha} B \end{bmatrix} x \approx \begin{bmatrix} b \\
  \sqrt{\alpha} d \end{bmatrix}$$
if and only if $x$ minimizes $\|Ax - b\|^2 + \alpha \|Bx - d\|^2$. This is the stacked form
(6.1.11), (6.1.20) of [golub2013matrix]. -/
theorem isLeastSquaresSolution_fromRows_iff {m₁ m₂ : Type*} [Fintype m₁] [Fintype m₂]
    (A : Matrix m₁ n 𝕜) (B : Matrix m₂ n 𝕜) (b : m₁ → 𝕜)
    (d : m₂ → 𝕜) {α : ℝ} (hα : 0 ≤ α) (x : EuclideanSpace 𝕜 n) :
    IsLeastSquaresSolution (fromRows A ((Real.sqrt α : 𝕜) • B))
        (WithLp.toLp 2 (Sum.elim b ((Real.sqrt α : 𝕜) • d))) x ↔
      ∀ y, ‖toEuclideanLin A x - WithLp.toLp 2 b‖ ^ 2
          + α * ‖toEuclideanLin B x - WithLp.toLp 2 d‖ ^ 2
        ≤ ‖toEuclideanLin A y - WithLp.toLp 2 b‖ ^ 2
          + α * ‖toEuclideanLin B y - WithLp.toLp 2 d‖ ^ 2 := by
  have hsq : ∀ y : EuclideanSpace 𝕜 n,
      ‖toEuclideanLin (fromRows A ((Real.sqrt α : 𝕜) • B)) y
          - WithLp.toLp 2 (Sum.elim b ((Real.sqrt α : 𝕜) • d))‖ ^ 2
        = ‖toEuclideanLin A y - WithLp.toLp 2 b‖ ^ 2
          + α * ‖toEuclideanLin B y - WithLp.toLp 2 d‖ ^ 2 := by
    intro y
    have hB : ‖toEuclideanLin ((Real.sqrt α : 𝕜) • B) y
        - WithLp.toLp 2 ((Real.sqrt α : 𝕜) • d)‖ ^ 2
          = α * ‖toEuclideanLin B y - WithLp.toLp 2 d‖ ^ 2 := by
      rw [toEuclideanLin_smul_apply, WithLp.toLp_smul, ← smul_sub, norm_smul, mul_pow,
        RCLike.norm_ofReal, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hα]
    rw [norm_fromRows_sub_sq, hB]
  simp only [IsLeastSquaresSolution]
  refine forall_congr' fun y => ?_
  rw [← hsq, ← hsq]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).symm

end Stacking

/-! ### General-form Tikhonov regularization -/

section GeneralForm

variable [DecidableEq m]

omit [DecidableEq n] [DecidableEq m] in
open scoped ComplexOrder in
/-- Let $A \in \mathbb{K}^{m \times n}$, $B \in \mathbb{K}^{p \times n}$ and $\alpha > 0$. Then
$A^H A + \alpha B^H B$ is positive definite if and only if $\ker A \cap \ker B = 0$. Hence
general-form Tikhonov regularization is well posed exactly in this case, as in §6.1.5 of
[golub2013matrix].

The matrix is $C^H C$ for the stacked matrix $C = \begin{bmatrix} A \\ \sqrt{\alpha} B
\end{bmatrix}$. -/
theorem posDef_gram_add_smul_gram_iff (A : Matrix m n 𝕜) (B : Matrix p n 𝕜) {α : ℝ}
    (hα : 0 < α) :
    (Aᴴ * A + (α : 𝕜) • (Bᴴ * B)).PosDef ↔
      LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥ := by
  classical
  constructor
  · intro h
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hA, hB⟩ := Submodule.mem_inf.1 hx
    rw [LinearMap.mem_ker, mulVecLin_apply] at hA hB
    by_contra hx
    have := (posDef_iff_dotProduct_mulVec.1 h).2 hx
    rw [add_mulVec, smul_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hA, hB, mulVec_zero,
      mulVec_zero, smul_zero, add_zero, dotProduct_zero] at this
    exact lt_irrefl _ this
  · intro h
    set C : Matrix (m ⊕ p) n 𝕜 := fromRows A ((Real.sqrt α : 𝕜) • B) with hC
    have hCC : Cᴴ * C = Aᴴ * A + (α : 𝕜) • (Bᴴ * B) := by
      rw [hC, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows,
        conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, RCLike.star_def,
        RCLike.conj_ofReal, ← RCLike.ofReal_mul, Real.mul_self_sqrt hα.le]
    rw [← hCC]
    refine PosDef.conjTranspose_mul_self C fun x y hxy => ?_
    rw [← sub_eq_zero] at hxy ⊢
    rw [← mulVec_sub, hC, fromRows_mulVec] at hxy
    have hs : (Real.sqrt α : 𝕜) ≠ 0 := by
      simpa using (Real.sqrt_pos.2 hα).ne'
    have hA : x - y ∈ LinearMap.ker A.mulVecLin := by
      rw [LinearMap.mem_ker, mulVecLin_apply]
      exact funext fun i => congrFun hxy (Sum.inl i)
    have hB : x - y ∈ LinearMap.ker B.mulVecLin := by
      have h2 : ((Real.sqrt α : 𝕜) • B) *ᵥ (x - y) = 0 :=
        funext fun i => congrFun hxy (Sum.inr i)
      rw [smul_mulVec, smul_eq_zero] at h2
      rw [LinearMap.mem_ker, mulVecLin_apply]
      exact h2.resolve_left hs
    have : x - y ∈ LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin :=
      Submodule.mem_inf.2 ⟨hA, hB⟩
    rw [h] at this
    exact this

/-- Let $A \in \mathbb{K}^{m \times n}$, $B \in \mathbb{K}^{p \times n}$ and
$\alpha \in \mathbb{R}$. The **general-form Tikhonov regularization** is the matrix
$$(A^H A + \alpha B^H B)^{-1} A^H \in \mathbb{K}^{n \times m}.$$
For $\alpha > 0$ and $\ker A \cap \ker B = 0$, it maps $b$ to the solution of
$\min \|Ax - b\|^2 + \alpha \|Bx\|^2$ (`Matrix.eq_toEuclideanLin_generalFormTikhonov_iff`). This
is (6.1.20)–(6.1.21) of [golub2013matrix].

If $A^H A + \alpha B^H B$ is singular, the matrix is $0$. -/
noncomputable def generalFormTikhonov (A : Matrix m n 𝕜) (B : Matrix p n 𝕜) (α : ℝ) :
    Matrix n m 𝕜 :=
  (Aᴴ * A + (α : 𝕜) • (Bᴴ * B))⁻¹ * Aᴴ

omit [DecidableEq m] in
/-- For $B = I$, general-form Tikhonov regularization is standard Tikhonov regularization: $(A^H A +
\alpha I)^{-1} A^H = (\alpha I + A^H A)^{-1} A^H$. -/
theorem generalFormTikhonov_one (A : Matrix m n 𝕜) (α : ℝ) :
    generalFormTikhonov A (1 : Matrix n n 𝕜) α = A.tikhonov α := by
  rw [generalFormTikhonov, tikhonov_def, conjTranspose_one, Matrix.mul_one, add_comm]

open scoped ComplexOrder in
/-- Let $A \in \mathbb{K}^{m \times n}$, $B \in \mathbb{K}^{p \times n}$, $\alpha > 0$ with
$\ker A \cap \ker B = 0$, and $b \in \mathbb{K}^m$. For $x \in \mathbb{K}^n$, the following are
equivalent: $x = (A^H A + \alpha B^H B)^{-1} A^H b$; $x$ solves
$(A^H A + \alpha B^H B) x = A^H b$; $x$ minimizes $y \mapsto \|Ay - b\|^2 + \alpha \|By\|^2$.
This is (6.1.20)–(6.1.21) of [golub2013matrix].

The statement is the conjunction of the first equivalence with each of the other two. -/
theorem eq_toEuclideanLin_generalFormTikhonov_iff (A : Matrix m n 𝕜) (B : Matrix p n 𝕜)
    {α : ℝ} (hα : 0 < α) (hAB : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥)
    (b : EuclideanSpace 𝕜 m) (x : EuclideanSpace 𝕜 n) :
    (x = toEuclideanLin (generalFormTikhonov A B α) b ↔
      toEuclideanLin (Aᴴ * A + (α : 𝕜) • (Bᴴ * B)) x = toEuclideanLin Aᴴ b) ∧
    (x = toEuclideanLin (generalFormTikhonov A B α) b ↔
      IsMinOn (fun y => ‖toEuclideanLin A y - b‖ ^ 2 + α * ‖toEuclideanLin B y‖ ^ 2)
        Set.univ x) := by
  have hM := ((posDef_gram_add_smul_gram_iff A B hα).2 hAB).isUnit
  have hne : ∀ v : EuclideanSpace 𝕜 n, v ≠ 0 →
      0 < ‖toEuclideanLin A v‖ ^ 2 + α * ‖toEuclideanLin B v‖ ^ 2 := by
    intro v hv
    by_contra hle'
    have hA : ‖toEuclideanLin A v‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖toEuclideanLin A v‖, sq_nonneg ‖toEuclideanLin B v‖]
    have hB : ‖toEuclideanLin B v‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖toEuclideanLin A v‖, sq_nonneg ‖toEuclideanLin B v‖]
    rw [pow_eq_zero_iff two_ne_zero, norm_eq_zero] at hA hB
    have hmem : WithLp.ofLp v ∈ LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin := by
      refine Submodule.mem_inf.2 ⟨?_, ?_⟩
      · rw [LinearMap.mem_ker, mulVecLin_apply]
        exact congrArg WithLp.ofLp hA
      · rw [LinearMap.mem_ker, mulVecLin_apply]
        exact congrArg WithLp.ofLp hB
    rw [hAB] at hmem
    exact hv (by simpa using hmem)
  have h1 : ∀ x : EuclideanSpace 𝕜 n, x = toEuclideanLin (generalFormTikhonov A B α) b ↔
      toEuclideanLin (Aᴴ * A + (α : 𝕜) • (Bᴴ * B)) x = toEuclideanLin Aᴴ b := by
    intro x
    constructor
    · rintro rfl
      rw [generalFormTikhonov, ← toEuclideanLin_mul_apply, ← Matrix.mul_assoc,
        mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hM), Matrix.one_mul]
    · intro h
      rw [generalFormTikhonov, toEuclideanLin_mul_apply, ← h,
        toEuclideanLin_nonsing_inv_mul_apply hM]
  refine ⟨h1 x, ?_⟩
  rw [isMinOn_univ_iff]
  set z := toEuclideanLin (generalFormTikhonov A B α) b with hzdef
  have hz := (h1 z).1 rfl
  have key := fun y => norm_sub_sq_add_mul_norm_sq_eq_of_gram_add_smul_gram A B α b hz y
  constructor
  · rintro rfl y
    rw [key y]
    nlinarith [sq_nonneg ‖toEuclideanLin A (y - z)‖, sq_nonneg ‖toEuclideanLin B (y - z)‖]
  · intro h
    have h2 := h z
    rw [key x] at h2
    by_contra hxz
    have := hne (x - z) (sub_ne_zero.2 hxz)
    linarith

open scoped ComplexOrder in
/-- Let $A \in \mathbb{K}^{m \times n}$, $\alpha > 0$ and $b \in \mathbb{K}^m$. Then
$x = (\alpha I + A^H A)^{-1} A^H b$ if and only if $x$ minimizes
$y \mapsto \|Ay - b\|^2 + \alpha \|y\|^2$. So the ridge solution $x(\alpha)$ is the unique
minimizer. This is ridge regression, (6.1.11)–(6.1.12) of [golub2013matrix].

This is the general form at $B = I$ (`Matrix.generalFormTikhonov_one`), where $\ker B = 0$. -/
theorem eq_toEuclideanLin_tikhonov_iff_isMinOn (A : Matrix m n 𝕜) {α : ℝ} (hα : 0 < α)
    (b : EuclideanSpace 𝕜 m) (x : EuclideanSpace 𝕜 n) :
    x = toEuclideanLin (A.tikhonov α) b ↔
      IsMinOn (fun y => ‖toEuclideanLin A y - b‖ ^ 2 + α * ‖y‖ ^ 2) Set.univ x := by
  have hker : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker (1 : Matrix n n 𝕜).mulVecLin = ⊥ :=
    eq_bot_iff.2 fun v hv => by
      have := (Submodule.mem_inf.1 hv).2
      rw [LinearMap.mem_ker, mulVecLin_apply, one_mulVec] at this
      rw [this]
      exact Submodule.zero_mem _
  simpa only [generalFormTikhonov_one, toEuclideanLin_one_apply] using
    (eq_toEuclideanLin_generalFormTikhonov_iff A 1 hα hker b x).2

end GeneralForm

/-! ### Leave-one-out cross-validation -/

section DeleteRow

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] [DecidableEq m]

omit [DecidableEq m] in
/-- For $A \in \mathbb{R}^{m \times n}$ and $\alpha \in \mathbb{R}$, the Tikhonov matrix is
$(A^T A + \alpha I)^{-1} A^T$. -/
theorem tikhonov_eq_real (A : Matrix m n ℝ) (α : ℝ) :
    A.tikhonov α = (Aᵀ * A + α • 1)⁻¹ * Aᵀ := by
  rw [tikhonov_def, conjTranspose_eq_transpose_of_trivial, add_comm]
  rfl

omit [DecidableEq m] [Fintype n] in
/-- For $A \in \mathbb{R}^{m \times n}$ and $\alpha > 0$, the matrix $A^T A + \alpha I$ is positive
definite. -/
theorem posDef_transpose_mul_self_add_smul_one [Finite n] (A : Matrix m n ℝ) {α : ℝ}
    (hα : 0 < α) : (Aᵀ * A + α • (1 : Matrix n n ℝ)).PosDef := by
  cases nonempty_fintype n
  have h : (Aᵀ * A).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using posSemidef_conjTranspose_mul_self A
  exact PosDef.posSemidef_add h (PosDef.one.smul hα)

omit [DecidableEq m] in
/-- Let $A \in \mathbb{R}^{m \times n}$ with rows $a_k^T$, and let $\alpha > 0$. Then for every $k$,
the **leave-one-out denominator** is positive:
$$a_k^T (A^T A + \alpha I)^{-1} a_k < 1.$$
This is the denominator of (6.1.16)–(6.1.17) of [golub2013matrix].

With $z = (A^T A + \alpha I)^{-1} a_k$ and $t = a_k^T z$, we have $t = \|Az\|^2 + \alpha \|z\|^2
\ge t^2 + \alpha \|z\|^2$, so $t < 1$ unless $z = 0$, and then $t = 0$. -/
theorem one_sub_dotProduct_inv_gram_pos (A : Matrix m n ℝ) {α : ℝ} (hα : 0 < α) (k : m) :
    0 < 1 - A k ⬝ᵥ ((Aᵀ * A + α • 1)⁻¹ *ᵥ A k) := by
  set M := Aᵀ * A + α • (1 : Matrix n n ℝ) with hM
  have hMpd := posDef_transpose_mul_self_add_smul_one A hα
  set z := M⁻¹ *ᵥ A k with hz
  have hMz : M *ᵥ z = A k := mulVec_nonsing_inv_mulVec hMpd.isUnit _
  set t := A k ⬝ᵥ z with ht
  have hquad : t = (A *ᵥ z) ⬝ᵥ (A *ᵥ z) + α * (z ⬝ᵥ z) := by
    rw [ht, ← hMz, dotProduct_comm, hM, add_mulVec, dotProduct_add, ← mulVec_mulVec,
      dotProduct_mulVec, vecMul_transpose, smul_mulVec, one_mulVec, dotProduct_smul,
      smul_eq_mul]
  have hk : (A *ᵥ z) k = t := rfl
  have hge : t ^ 2 ≤ (A *ᵥ z) ⬝ᵥ (A *ᵥ z) := by
    rw [← hk, sq]
    exact Finset.single_le_sum (f := fun i => (A *ᵥ z) i * (A *ᵥ z) i)
      (fun i _ => mul_self_nonneg _) (Finset.mem_univ k)
  by_cases hz0 : z = 0
  · have : t = 0 := by rw [ht, hz0, dotProduct_zero]
    rw [this]; norm_num
  · have hpos : 0 < z ⬝ᵥ z := by
      have hz' : 0 ≤ z ⬝ᵥ z := by simpa using dotProduct_self_star_nonneg z
      rcases hz'.lt_or_eq with h | h
      · exact h
      · exact absurd (dotProduct_self_eq_zero.1 h.symm) hz0
    nlinarith [mul_pos hα hpos]

omit [Fintype n] [DecidableEq n] in
/-- Deleting row $k$ of $A$ by $D_k = \operatorname{diag}(1, \dots, 0, \dots, 1)$ gives
$(D_k A)^T (D_k A) = A^T A - a_k a_k^T$. -/
private theorem transpose_mul_diagonal_mul_self (A : Matrix m n ℝ) (k : m) :
    (diagonal (Function.update (1 : m → ℝ) k 0) * A)ᵀ *
        (diagonal (Function.update (1 : m → ℝ) k 0) * A)
      = Aᵀ * A - vecMulVec (A k) (A k) := by
  have hdd : (fun i => Function.update (1 : m → ℝ) k 0 i * Function.update (1 : m → ℝ) k 0 i)
      = Function.update (1 : m → ℝ) k 0 := by
    funext i
    by_cases h : i = k
    · simp [h]
    · simp [h]
  have h := conjTranspose_mul_diagonal_update_mul A 1 k 0
  rw [show diagonal (1 : m → ℝ) = 1 from diagonal_one, Matrix.mul_one, Pi.one_apply, zero_sub,
    neg_one_smul, ← sub_eq_add_neg, conjTranspose_eq_transpose_of_trivial] at h
  rw [transpose_mul, diagonal_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _),
    diagonal_mul_diagonal, hdd, ← Matrix.mul_assoc, h]

omit [Fintype n] [DecidableEq n] in
/-- Deleting row $k$ on the right-hand side gives $(D_k A)^T (D_k b) = A^T b - b_k a_k$. -/
private theorem transpose_mulVec_diagonal_mulVec (A : Matrix m n ℝ) (b : m → ℝ) (k : m) :
    (diagonal (Function.update (1 : m → ℝ) k 0) * A)ᵀ *ᵥ
        (diagonal (Function.update (1 : m → ℝ) k 0) *ᵥ b)
      = Aᵀ *ᵥ b - b k • A k := by
  have hdd : (fun i => Function.update (1 : m → ℝ) k 0 i * Function.update (1 : m → ℝ) k 0 i)
      = Function.update (1 : m → ℝ) k 0 := by
    funext i
    by_cases h : i = k
    · simp [h]
    · simp [h]
  have h := conjTranspose_mul_diagonal_update_mulVec A 1 k 0 b
  rw [show diagonal (1 : m → ℝ) = 1 from diagonal_one, Matrix.mul_one, Pi.one_apply, zero_sub,
    neg_one_mul, neg_smul, ← sub_eq_add_neg, conjTranspose_eq_transpose_of_trivial] at h
  rw [transpose_mul, diagonal_transpose, mulVec_mulVec, Matrix.mul_assoc, diagonal_mul_diagonal,
    hdd, h]

/-- Let $A \in \mathbb{R}^{m \times n}$ with rows $a_k^T$, $b \in \mathbb{R}^m$ and $\alpha > 0$,
and let $x = (A^T A + \alpha I)^{-1} A^T b$ be the ridge solution. Let $D_k =
\operatorname{diag}(1, \dots, 0, \dots, 1)$ delete equation $k$, and let
$z_k = (A^T A + \alpha I)^{-1} a_k$. Then the ridge solution of the reduced problem
$(D_k A) x \approx D_k b$ is
$$x_k = x + \frac{a_k^T x - b_k}{1 - z_k^T a_k} z_k.$$
This is (6.1.16) of [golub2013matrix].

The formula is the Sherman–Morrison formula for the rank-one downdate
$(D_k A)^T (D_k A) = A^T A - a_k a_k^T$. The matrix $D_k$ is `diagonal (Function.update 1 k 0)`. -/
theorem tikhonov_deleteRow_eq (A : Matrix m n ℝ) (b : m → ℝ) {α : ℝ} (hα : 0 < α) (k : m) :
    (diagonal (Function.update (1 : m → ℝ) k 0) * A).tikhonov α *ᵥ
        (diagonal (Function.update (1 : m → ℝ) k 0) *ᵥ b)
      = A.tikhonov α *ᵥ b + ((A k ⬝ᵥ (A.tikhonov α *ᵥ b) - b k) /
          (1 - ((Aᵀ * A + α • 1)⁻¹ *ᵥ A k) ⬝ᵥ A k)) • ((Aᵀ * A + α • 1)⁻¹ *ᵥ A k) := by
  set D := diagonal (Function.update (1 : m → ℝ) k 0) with hD
  set M := Aᵀ * A + α • (1 : Matrix n n ℝ) with hM
  have hMpd : M.PosDef := posDef_transpose_mul_self_add_smul_one A hα
  have hMkpd := posDef_transpose_mul_self_add_smul_one (D * A) hα
  have hMk : (D * A)ᵀ * (D * A) + α • (1 : Matrix n n ℝ) = M - vecMulVec (A k) (A k) := by
    rw [hD, transpose_mul_diagonal_mul_self, hM]
    abel
  rw [hMk] at hMkpd
  set z := M⁻¹ *ᵥ A k with hz
  set x := A.tikhonov α *ᵥ b with hx
  have hMx : M *ᵥ x = Aᵀ *ᵥ b := by
    rw [hx, tikhonov_eq_real, ← mulVec_mulVec]
    exact mulVec_nonsing_inv_mulVec hMpd.isUnit _
  have hMz : M *ᵥ z = A k := mulVec_nonsing_inv_mulVec hMpd.isUnit _
  have ht : 0 < 1 - z ⬝ᵥ A k := by
    rw [dotProduct_comm]; exact one_sub_dotProduct_inv_gram_pos A hα k
  set c := (A k ⬝ᵥ x - b k) / (1 - z ⬝ᵥ A k) with hc
  have hc' : c * (1 - z ⬝ᵥ A k) = A k ⬝ᵥ x - b k := div_mul_cancel₀ _ ht.ne'
  have key : (M - vecMulVec (A k) (A k)) *ᵥ (x + c • z) = Aᵀ *ᵥ b - b k • A k := by
    rw [sub_mulVec, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, hMx, hMz,
      vecMulVec_mulVec, vecMulVec_mulVec, op_smul_eq_smul, op_smul_eq_smul,
      dotProduct_comm (A k) z]
    linear_combination (norm := module) hc' • A k
  rw [tikhonov_eq_real, ← mulVec_mulVec, hD, transpose_mulVec_diagonal_mulVec, ← hD, hMk, ← key,
    nonsing_inv_mulVec_mulVec hMkpd.isUnit]

/-- Let $A \in \mathbb{R}^{m \times n}$ with rows $a_k^T$, $b \in \mathbb{R}^m$ and $\alpha > 0$,
let $H = A (A^T A + \alpha I)^{-1} A^T$ be the ridge hat matrix, and let $x_k$ be the ridge
solution with equation $k$ deleted. Then the **leave-one-out residual** is
$$b_k - a_k^T x_k = \frac{((I - H) b)_k}{(I - H)_{kk}}, \qquad (I - H)_{kk} > 0.$$
This is (6.1.17) of [golub2013matrix]. -/
theorem tikhonov_deleteRow_residual_eq (A : Matrix m n ℝ) (b : m → ℝ) {α : ℝ} (hα : 0 < α)
    (k : m) :
    b k - A k ⬝ᵥ ((diagonal (Function.update (1 : m → ℝ) k 0) * A).tikhonov α *ᵥ
        (diagonal (Function.update (1 : m → ℝ) k 0) *ᵥ b))
      = ((1 - A * (Aᵀ * A + α • 1)⁻¹ * Aᵀ : Matrix m m ℝ) *ᵥ b) k /
          (1 - A * (Aᵀ * A + α • 1)⁻¹ * Aᵀ : Matrix m m ℝ) k k ∧
    0 < (1 - A * (Aᵀ * A + α • 1)⁻¹ * Aᵀ : Matrix m m ℝ) k k := by
  set M := Aᵀ * A + α • (1 : Matrix n n ℝ) with hM
  have hkk : (1 - A * M⁻¹ * Aᵀ : Matrix m m ℝ) k k = 1 - A k ⬝ᵥ (M⁻¹ *ᵥ A k) := by
    rw [Matrix.sub_apply, one_apply_eq]
    congr 1
    simp only [Matrix.mul_apply, mulVec, dotProduct, transpose_apply, Finset.sum_mul,
        Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  have hpos : 0 < 1 - A k ⬝ᵥ (M⁻¹ *ᵥ A k) := one_sub_dotProduct_inv_gram_pos A hα k
  refine ⟨?_, hkk ▸ hpos⟩
  have hHb : ((1 - A * M⁻¹ * Aᵀ : Matrix m m ℝ) *ᵥ b) k
      = b k - A k ⬝ᵥ (A.tikhonov α *ᵥ b) := by
    rw [sub_mulVec, one_mulVec, Pi.sub_apply, tikhonov_eq_real, ← mulVec_mulVec,
      ← mulVec_mulVec, ← mulVec_mulVec]
    rfl
  rw [hHb, hkk, tikhonov_deleteRow_eq A b hα k, ← hM, dotProduct_add, dotProduct_smul,
    smul_eq_mul, dotProduct_comm (M⁻¹ *ᵥ A k) (A k)]
  have ht : (1 : ℝ) - A k ⬝ᵥ (M⁻¹ *ᵥ A k) ≠ 0 := hpos.ne'
  field_simp
  ring

end DeleteRow

end IndexTypes

/-! ### Expansions in a singular value decomposition -/

section IsSVD

variable {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ}

variable {A : Matrix (Fin m) (Fin n) 𝕜} {U : Matrix (Fin m) (Fin m) 𝕜} {σ : ℕ → ℝ}
  {V : Matrix (Fin n) (Fin n) 𝕜}

/-- Let $A \in \mathbb{K}^{m \times n}$ have the singular value decomposition $U^H A V = \Sigma$
with singular values $\sigma_i$, and let $\alpha > 0$. Then
$$(\alpha I + A^H A)^{-1} A^H = V \operatorname{diag}\Bigl(\frac{\sigma_i}{\sigma_i^2 +
  \alpha}\Bigr) U^H,$$
with the rectangular diagonal matrix of size $n \times m$.

The singular value decomposition is `Matrix.IsSVD`, and the diagonal matrix is
`Matrix.rectDiagonal`. -/
theorem IsSVD.tikhonov_eq (h : IsSVD A U σ V) {α : ℝ} (hα : 0 < α) :
    A.tikhonov α = V * (rectDiagonal fun i => ((σ i / (σ i ^ 2 + α) : ℝ) : 𝕜) :
      Matrix (Fin n) (Fin m) 𝕜) * star U := by
  have hdet := A.isUnit_det_smul_one_add_gram α hα
  set S : Matrix (Fin m) (Fin n) 𝕜 := rectDiagonal fun i => ((σ i : ℝ) : 𝕜) with hS
  set D : Matrix (Fin n) (Fin m) 𝕜 := rectDiagonal fun i => ((σ i / (σ i ^ 2 + α) : ℝ) : 𝕜)
    with hD
  have hA : A = U * S * star V := h.eq_mul_mul_star
  have hU : star U * U = 1 := mem_unitaryGroup_iff'.1 h.mem_unitaryGroup_left
  have hV : V * star V = 1 := mem_unitaryGroup_iff.1 h.mem_unitaryGroup_right
  have hV' : star V * V = 1 := mem_unitaryGroup_iff'.1 h.mem_unitaryGroup_right
  have hAh : Aᴴ = V * Sᴴ * star U := by
    rw [hA, conjTranspose_mul, conjTranspose_mul, ← star_eq_conjTranspose (star V), star_star,
      star_eq_conjTranspose, Matrix.mul_assoc]
  have hAA : Aᴴ * A = V * (Sᴴ * S) * star V := by
    rw [hAh, hA]
    calc V * Sᴴ * star U * (U * S * star V) = V * Sᴴ * (star U * U) * S * star V := by
          simp only [Matrix.mul_assoc]
      _ = V * (Sᴴ * S) * star V := by rw [hU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hconj : (α : 𝕜) • (1 : Matrix (Fin n) (Fin n) 𝕜) + V * (Sᴴ * S) * star V
      = V * ((α : 𝕜) • 1 + Sᴴ * S) * star V := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hV]
  have hdiag : ((α : 𝕜) • 1 + Sᴴ * S) * D = Sᴴ := by
    rw [hS, conjTranspose_rectDiagonal_mul_self, smul_one_eq_diagonal, diagonal_add,
      rectDiagonal_conjTranspose]
    ext i j
    rw [diagonal_mul, hD, rectDiagonal_apply, rectDiagonal_apply]
    by_cases hij : (i : ℕ) = j
    · have him : (i : ℕ) < m := hij ▸ j.isLt
      rw [ite_eq_left hij, ite_eq_left hij, ite_eq_left him, Function.comp_apply]
      have hpos : (0 : ℝ) < σ i ^ 2 + α := by positivity
      have hne : ((σ i : ℝ) : 𝕜) ^ 2 + (α : 𝕜) ≠ 0 := by exact_mod_cast hpos.ne'
      simp only [RCLike.star_def, RCLike.conj_ofReal]
      push_cast
      field_simp
      ring
    · rw [ite_eq_right hij, ite_eq_right hij, mul_zero]
  have hmul : ((α : 𝕜) • 1 + Aᴴ * A) * (V * D * star U) = Aᴴ := by
    rw [hAA, hconj]
    calc V * ((α : 𝕜) • 1 + Sᴴ * S) * star V * (V * D * star U)
        = V * (((α : 𝕜) • 1 + Sᴴ * S) * (star V * V) * D) * star U := by
          simp only [Matrix.mul_assoc]
      _ = Aᴴ := by rw [hV', Matrix.mul_one, hdiag, hAh, Matrix.mul_assoc]
  calc A.tikhonov α = ((α : 𝕜) • 1 + Aᴴ * A)⁻¹ * (((α : 𝕜) • 1 + Aᴴ * A) * (V * D * star U)) := by
        rw [hmul, tikhonov_def]
    _ = V * D * star U := by rw [← Matrix.mul_assoc, nonsing_inv_mul _ hdet, Matrix.one_mul]

/-- Let $A \in \mathbb{K}^{m \times n}$ have the singular value decomposition $U^H A V = \Sigma$,
with columns $u_i$ of $U$, $v_i$ of $V$, and singular values $\sigma_i$. Then for $\alpha > 0$
and $b \in \mathbb{K}^m$, the ridge solution is
$$x(\alpha) = \sum_{i = 1}^{\min(m, n)} \frac{\sigma_i \langle u_i, b \rangle}{\sigma_i^2 +
  \alpha} v_i.$$
This is (6.1.14) of [golub2013matrix].

The terms with $\sigma_i = 0$ vanish. Lean indices start at $0$. -/
theorem toEuclideanLin_tikhonov_eq_sum_of_isSVD (h : IsSVD A U σ V) {α : ℝ} (hα : 0 < α)
    (b : EuclideanSpace 𝕜 (Fin m)) :
    toEuclideanLin (A.tikhonov α) b
      = ∑ i : Fin (min m n), ((σ i / (σ i ^ 2 + α) : ℝ) : 𝕜) • inner 𝕜
          (WithLp.toLp 2 (Uᵀ (Fin.castLE (min_le_left m n) i)) : EuclideanSpace 𝕜 (Fin m)) b •
          (WithLp.toLp 2 (Vᵀ (Fin.castLE (min_le_right m n) i)) : EuclideanSpace 𝕜 (Fin n)) := by
  rw [h.tikhonov_eq hα, toEuclideanLin_mul_rectDiagonal_mul_star_apply]

/-- Let $A \in \mathbb{K}^{m \times n}$ have the singular value decomposition $U^H A V = \Sigma$,
with columns $u_i$ of $U$ and singular values $\sigma_i$. Then for $\alpha > 0$ and
$b \in \mathbb{K}^m$,
$$\|x(\alpha)\|^2 = \sum_{i = 1}^{\min(m, n)} \Bigl(\frac{\sigma_i |\langle u_i, b
  \rangle|}{\sigma_i^2 + \alpha}\Bigr)^2.$$
This is the secular function of §6.2.1 of [golub2013matrix]. -/
theorem norm_sq_toEuclideanLin_tikhonov_eq_sum_of_isSVD (h : IsSVD A U σ V) {α : ℝ} (hα : 0 < α)
    (b : EuclideanSpace 𝕜 (Fin m)) :
    ‖toEuclideanLin (A.tikhonov α) b‖ ^ 2
      = ∑ i : Fin (min m n), (σ i * ‖inner 𝕜
          (WithLp.toLp 2 (Uᵀ (Fin.castLE (min_le_left m n) i)) : EuclideanSpace 𝕜 (Fin m)) b‖
            / (σ i ^ 2 + α)) ^ 2 := by
  rw [h.tikhonov_eq hα,
    norm_sq_toEuclideanLin_mul_rectDiagonal_mul_star_apply U h.mem_unitaryGroup_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hpos : (0 : ℝ) < σ i ^ 2 + α := by positivity
  rw [RCLike.norm_ofReal, abs_of_nonneg (div_nonneg (h.nonneg i) hpos.le)]
  ring

/-- Let $A \in \mathbb{K}^{m \times n}$ have the singular value decomposition $U^H A V = \Sigma$,
with columns $u_i$ of $U$, $v_i$ of $V$, and singular values $\sigma_i$. Then for every
$b \in \mathbb{K}^m$, the least-squares solution of least norm is
$$A^+ b = \sum_{i = 1}^{\min(m, n)} \sigma_i^{-1} \langle u_i, b \rangle v_i,$$
where $0^{-1} = 0$. This is (6.2.3) and (5.3.2) of [golub2013matrix]. -/
theorem toEuclideanLin_pinv_eq_sum_of_isSVD (h : IsSVD A U σ V) (b : EuclideanSpace 𝕜 (Fin m)) :
    toEuclideanLin A.pinv b
      = ∑ i : Fin (min m n), ((σ i : 𝕜))⁻¹ • inner 𝕜
          (WithLp.toLp 2 (Uᵀ (Fin.castLE (min_le_left m n) i)) : EuclideanSpace 𝕜 (Fin m)) b •
          (WithLp.toLp 2 (Vᵀ (Fin.castLE (min_le_right m n) i)) : EuclideanSpace 𝕜 (Fin n)) := by
  rw [h.pinv_eq, toEuclideanLin_mul_rectDiagonal_mul_star_apply]

/-- Let $A \in \mathbb{K}^{m \times n}$ have the singular value decomposition $U^H A V = \Sigma$,
with columns $u_i$ of $U$ and singular values $\sigma_i$. Then for every $b \in \mathbb{K}^m$,
$$\|A^+ b\|^2 = \sum_{i = 1}^{\min(m, n)} \Bigl(\frac{|\langle u_i, b
  \rangle|}{\sigma_i}\Bigr)^2,$$
where a quotient with $\sigma_i = 0$ is $0$. This is (6.2.3) of [golub2013matrix].

The Lean convention $x / 0 = 0$ drops the terms beyond the rank. -/
theorem norm_sq_toEuclideanLin_pinv_eq_sum_of_isSVD (h : IsSVD A U σ V)
    (b : EuclideanSpace 𝕜 (Fin m)) :
    ‖toEuclideanLin A.pinv b‖ ^ 2
      = ∑ i : Fin (min m n), (‖inner 𝕜
          (WithLp.toLp 2 (Uᵀ (Fin.castLE (min_le_left m n) i)) : EuclideanSpace 𝕜 (Fin m)) b‖
            / σ i) ^ 2 := by
  rw [h.pinv_eq,
    norm_sq_toEuclideanLin_mul_rectDiagonal_mul_star_apply U h.mem_unitaryGroup_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_inv, RCLike.norm_ofReal, abs_of_nonneg (h.nonneg i)]
  ring

/-- Let $A \in \mathbb{K}^{m \times n}$ have the singular value decomposition $U^H A V = \Sigma$,
with columns $u_i$ of $U$ and singular values $\sigma_i$, and let
$\tau_1, \tau_2, \dots \in \mathbb{K}$. For $x = V \operatorname{diag}(\tau_i) U^H b$, with the
rectangular diagonal matrix of size $n \times m$, the residual is
$$\|Ax - b\|^2 = \sum_{i = 1}^{m} |c_i - 1|^2 |\langle u_i, b \rangle|^2, \qquad c_i = \sigma_i
  \tau_i \text{ for } i \le n, \quad c_i = 0 \text{ for } i > n.$$
-/
theorem IsSVD.norm_sq_toEuclideanLin_sub (h : IsSVD A U σ V) (τ : ℕ → 𝕜)
    (b : EuclideanSpace 𝕜 (Fin m)) :
    ‖toEuclideanLin A (toEuclideanLin (V * (rectDiagonal τ : Matrix (Fin n) (Fin m) 𝕜) *
        star U) b) - b‖ ^ 2
      = ∑ i : Fin m, ‖(if (i : ℕ) < n then (σ i : 𝕜) * τ i else 0) - 1‖ ^ 2 *
          ‖inner 𝕜 (WithLp.toLp 2 (Uᵀ i) : EuclideanSpace 𝕜 (Fin m)) b‖ ^ 2 := by
  set S : Matrix (Fin m) (Fin n) 𝕜 := rectDiagonal fun i => ((σ i : ℝ) : 𝕜) with hS
  have hU' : U * star U = 1 := mem_unitaryGroup_iff.1 h.mem_unitaryGroup_left
  have hV' : star V * V = 1 := mem_unitaryGroup_iff'.1 h.mem_unitaryGroup_right
  set E : Matrix (Fin m) (Fin m) 𝕜 :=
    diagonal fun i => (if (i : ℕ) < n then (σ i : 𝕜) * τ i else 0) - 1 with hE
  have hSD : S * (rectDiagonal τ : Matrix (Fin n) (Fin m) 𝕜) - 1 = E := by
    rw [hS, rectDiagonal_mul_rectDiagonal, rectDiagonal_eq_diagonal, hE, ← diagonal_one,
      diagonal_sub]
  have hprod : A * (V * (rectDiagonal τ : Matrix (Fin n) (Fin m) 𝕜) * star U)
      = U * E * star U + 1 := by
    rw [← hSD, h.eq_mul_mul_star, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU']
    calc U * S * star V * (V * (rectDiagonal τ : Matrix (Fin n) (Fin m) 𝕜) * star U)
        = U * S * (star V * V) * (rectDiagonal τ : Matrix (Fin n) (Fin m) 𝕜) * star U := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV', Matrix.mul_one]; simp only [Matrix.mul_assoc, sub_add_cancel]
  have hres : toEuclideanLin A (toEuclideanLin (V * (rectDiagonal τ : Matrix (Fin n) (Fin m) 𝕜) *
      star U) b) - b = toEuclideanLin U (toEuclideanLin E (toEuclideanLin (star U) b)) := by
    rw [← toEuclideanLin_mul_apply, hprod, map_add, LinearMap.add_apply, toEuclideanLin_one,
      LinearMap.id_apply, add_sub_cancel_right, toEuclideanLin_mul_apply,
      toEuclideanLin_mul_apply]
  rw [hres, norm_toEuclideanLin_apply_of_mem_unitaryGroup h.mem_unitaryGroup_left,
    EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hE, toEuclideanLin_apply, WithLp.ofLp_toLp, mulVec_diagonal, norm_mul, mul_pow,
    toEuclideanLin_apply, WithLp.ofLp_toLp, star_mulVec_apply_eq_inner]

/-- Let $A \in \mathbb{K}^{m \times n}$ have the singular value decomposition $U^H A V = \Sigma$,
with columns $u_i$ of $U$ and singular values $\sigma_i$. Then for $\alpha > 0$ and
$b \in \mathbb{K}^m$, the ridge residual is
$$\|A x(\alpha) - b\|^2 = \|A A^+ b - b\|^2 + \sum_{\substack{1 \le i \le \min(m, n) \\ \sigma_i
  \ne 0}} \Bigl(\frac{\alpha |\langle u_i, b \rangle|}{\sigma_i^2 + \alpha}\Bigr)^2.$$
This is (6.2.4) of [golub2013matrix]. -/
theorem norm_sq_toEuclideanLin_tikhonov_sub_eq_sum_of_isSVD (h : IsSVD A U σ V) {α : ℝ} (hα : 0 < α)
    (b : EuclideanSpace 𝕜 (Fin m)) :
    ‖toEuclideanLin A (toEuclideanLin (A.tikhonov α) b) - b‖ ^ 2
      = ‖toEuclideanLin A (toEuclideanLin A.pinv b) - b‖ ^ 2
        + ∑ i ∈ Finset.univ.filter (fun i : Fin (min m n) => σ i ≠ 0),
          (α * ‖inner 𝕜 (WithLp.toLp 2 (Uᵀ (Fin.castLE (min_le_left m n) i)) :
            EuclideanSpace 𝕜 (Fin m)) b‖ / (σ i ^ 2 + α)) ^ 2 := by
  set g : Fin m → ℝ := fun i => if σ i ≠ 0 then
    (α * ‖inner 𝕜 (WithLp.toLp 2 (Uᵀ i) : EuclideanSpace 𝕜 (Fin m)) b‖ / (σ i ^ 2 + α)) ^ 2
    else 0 with hg
  have hre : ∑ i ∈ Finset.univ.filter (fun i : Fin (min m n) => σ i ≠ 0),
      (α * ‖inner 𝕜 (WithLp.toLp 2 (Uᵀ (Fin.castLE (min_le_left m n) i)) :
        EuclideanSpace 𝕜 (Fin m)) b‖ / (σ i ^ 2 + α)) ^ 2
        = ∑ i : Fin m, if (i : ℕ) < min m n then g i else 0 := by
    rw [Finset.sum_filter]
    exact Fin.sum_castLE_eq_sum_ite (min_le_left m n) g
  rw [hre, h.tikhonov_eq hα, h.pinv_eq, h.norm_sq_toEuclideanLin_sub,
    h.norm_sq_toEuclideanLin_sub, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hin : (i : ℕ) < n
  · have hmin : (i : ℕ) < min m n := lt_min i.isLt hin
    rw [ite_eq_left hin, ite_eq_left hin, ite_eq_left hmin]
    simp only [hg]
    by_cases hσ : σ i = 0
    · simp [hσ]
    · have hpos : (0 : ℝ) < σ i ^ 2 + α := by positivity
      have h1 : ((σ i : 𝕜)) * ((σ i / (σ i ^ 2 + α) : ℝ) : 𝕜) - 1
          = ((-(α / (σ i ^ 2 + α)) : ℝ) : 𝕜) := by
        have hne : ((σ i : ℝ) : 𝕜) ^ 2 + (α : 𝕜) ≠ 0 := by exact_mod_cast hpos.ne'
        push_cast
        field_simp
        ring
      have h2 : ((σ i : 𝕜)) * ((σ i : 𝕜))⁻¹ - 1 = 0 := by
        rw [mul_inv_cancel₀ (by exact_mod_cast hσ), sub_self]
      rw [h1, h2, RCLike.norm_ofReal, abs_neg, abs_of_pos (div_pos hα hpos),
        ite_eq_left (show σ i ≠ 0 from hσ)]
      simp only [norm_zero]
      ring
  · have hmin : ¬ (i : ℕ) < min m n := fun h => hin (lt_of_lt_of_le h (min_le_right m n))
    rw [ite_eq_right hin, ite_eq_right hin, ite_eq_right hmin, add_zero]

/-- Let $A \in \mathbb{K}^{m \times n}$ have the singular value decomposition $U^H A V = \Sigma$,
with columns $u_i$ of $U$, and let $r = \operatorname{rank} A$. Then for every
$b \in \mathbb{K}^m$, the least residual is
$$\|A A^+ b - b\|^2 = \sum_{i = r + 1}^{m} |\langle u_i, b \rangle|^2.$$
This is (5.3.3) and (5.5.2) of [golub2013matrix].

Lean indices start at $0$, so the sum is over the `i : Fin m` with `A.rank ≤ i`. -/
theorem norm_sub_sq_pinv_eq_sum_of_isSVD (h : IsSVD A U σ V) (b : EuclideanSpace 𝕜 (Fin m)) :
    ‖toEuclideanLin A (toEuclideanLin A.pinv b) - b‖ ^ 2
      = ∑ i ∈ Finset.univ.filter (fun i : Fin m => A.rank ≤ i),
          ‖inner 𝕜 (WithLp.toLp 2 (Uᵀ i) : EuclideanSpace 𝕜 (Fin m)) b‖ ^ 2 := by
  have hrn : A.rank ≤ n := (rank_le_card_width A).trans_eq (Fintype.card_fin n)
  rw [h.pinv_eq, h.norm_sq_toEuclideanLin_sub, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : A.rank ≤ (i : ℕ)
  · rw [ite_eq_left hi]
    have h0 : (if (i : ℕ) < n then ((σ i : 𝕜)) * ((σ i : 𝕜))⁻¹ else 0) = 0 := by
      split_ifs with hin
      · have : σ i = 0 := by
          rw [h.singularValues_eq i.isLt hin, sortedSingularValues_eq_zero_iff_rank_le]
          exact hi
        simp [this]
      · rfl
    rw [h0, zero_sub, norm_neg, norm_one, one_pow, one_mul]
  · rw [ite_eq_right hi]
    have hin : (i : ℕ) < n := by omega
    have hσ : σ i ≠ 0 := by
      rw [h.singularValues_eq i.isLt hin]
      intro h0
      rw [sortedSingularValues_eq_zero_iff_rank_le] at h0
      exact hi h0
    rw [ite_eq_left hin, mul_inv_cancel₀ (by exact_mod_cast hσ), sub_self, norm_zero]
    ring

end IsSVD

/-! ### General-form Tikhonov in GSVD coordinates -/

section IsGSVD

variable {𝕜 : Type*} [RCLike 𝕜]

variable {m n : ℕ}

/-- Let $A \in \mathbb{K}^{m \times n}$ with $n \le m$, let $B \in \mathbb{K}^{n \times n}$ be
invertible, and let $U_1^H A X = D_A$, $U_2^H B X = D_B$ be a GSVD with the numbers $\alpha_k$,
$\beta_k$ and the columns $x_k$ of $X$. Then for $\mu > 0$ and $b \in \mathbb{K}^m$, with
$\tilde b = U_1^H b$,
$$(A^H A + \mu B^H B)^{-1} A^H b = \sum_{k = 1}^{n} \frac{\alpha_k \tilde b_k}{\alpha_k^2 + \mu
  \beta_k^2} x_k.$$
This is (6.1.26) of [golub2013matrix] and the display before it, with the regularization
parameter $\lambda$ of the source written $\mu$.

For square invertible $B$, the GSVD has $p = 0$, $r = n$ and every $\beta_k > 0$. Since $X^H
(A^H A + \mu B^H B) X = \operatorname{diag}(\alpha_k^2 + \mu \beta_k^2)$
(`Matrix.IsGSVD.conjTranspose_mul_gram_add_smul_gram_mul`), we get $(A^H A + \mu B^H B)^{-1}
A^H = X \operatorname{diag}(\alpha_k^2 + \mu \beta_k^2)^{-1} D_A^H U_1^H$. -/
theorem generalFormTikhonov_mulVec_eq_sum_of_isGSVD {A : Matrix (Fin m) (Fin n) 𝕜}
    {B : Matrix (Fin n) (Fin n) 𝕜} (hB : IsUnit B) {U₁ : Matrix (Fin m) (Fin m) 𝕜}
    {U₂ X : Matrix (Fin n) (Fin n) 𝕜} {α β : ℕ → ℝ} (h : IsGSVD A B U₁ U₂ X α β)
    (hnm : n ≤ m) {μ : ℝ} (hμ : 0 < μ) (b : Fin m → 𝕜) :
    generalFormTikhonov A B μ *ᵥ b = ∑ k : Fin n,
      (((α k / (α k ^ 2 + μ * β k ^ 2) : ℝ) : 𝕜) * (star U₁ *ᵥ b) (Fin.castLE hnm k)) •
        X.col k := by
  classical
  have hker : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥ := by
    rw [(LinearMap.ker_eq_bot (f := B.mulVecLin)).2 (mulVec_injective_iff_isUnit.2 hB),
      inf_bot_eq]
  obtain ⟨hrn, -, -⟩ := h.rank_eq_and_ne_zero (linearIndependent_rows_of_isUnit hB) hker
  have hd0 : ∀ k : Fin n, α k ^ 2 + μ * β k ^ 2 ≠ 0 := fun k =>
    h.sq_add_smul_sq_ne_zero hμ (by rw [hrn]; exact k.isLt)
  rw [generalFormTikhonov, h.inv_gram_add_smul_gram_eq hnm μ hd0, Matrix.mul_assoc,
    Matrix.mul_assoc, h.conjTranspose_mul_conjTranspose_left, ← mulVec_mulVec, ← mulVec_mulVec,
    ← mulVec_mulVec]
  ext i
  simp only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, col_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm (X i k)]
  congr 1
  change (diagonal _ *ᵥ (rectDiagonal _ *ᵥ (star U₁ *ᵥ b))) k = _
  rw [mulVec_diagonal, rectDiagonal_mulVec _ _ _ (lt_of_lt_of_le k.isLt hnm)]
  simp only [Fin.castLE, mulVec, dotProduct]
  push_cast
  ring

end IsGSVD

end Matrix
