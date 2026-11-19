/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Subproblem.Matrix

/-!
# Conn, Gould and Toint, Section 7.4: The scaled Euclidean trust-region problem

Section 7.4 of [conn2000trust] treats the trust-region subproblem in the norm
$\|s\|_M = \sqrt{s^T M s}$ of a symmetric positive definite matrix $M \in \mathbb{R}^{n \times n}$:
$$\min_{s} \; m(s) = g^T s + \tfrac{1}{2} s^T H s \quad \text{subject to} \quad \|s\|_M \le \Delta.
  \qquad (7.4.1)$$
The module shows that (7.4.1) is the Euclidean ball problem in two sets of coordinates:
intrinsically, in the inner product $\langle x, y \rangle_M = x^T M y$ with gradient $M^{-1} g$ and
operator $M^{-1} H$, and explicitly, after a congruence $S^T M S = I$ as in (7.4.2)–(7.4.4). It then
proves Theorem 7.4.1, the characterization of the global minimizers of (7.4.1). The proofs use the
scaled space of `Numlib.Optimization.Subproblem.Matrix` and the ball characterization
`Subproblem.isMinOn_closedBall_iff`.

## Main definitions

* Section 7.4, `ConnGouldToint.Chapter07.mNorm`: the norm $\|s\|_M = \sqrt{s^T M s}$.
* Equation (7.4.1), `ConnGouldToint.Chapter07.matrixQuadModel`: the quadratic model
  $m(s) = g^T s + \frac{1}{2} s^T H s$.
* Equation (7.4.1), `ConnGouldToint.Chapter07.weightedTrustRegion`: the feasible set
  $\{s : \|s\|_M \le \Delta\}$.

## Main results

* Equations (7.4.1)–(7.4.4), `ConnGouldToint.Chapter07.isMinOn_weightedTrustRegion_iff_scaled`: $s$
  solves (7.4.1) if and only if it solves the ball problem in the $M$-inner product with gradient
  $M^{-1} g$ and operator $M^{-1} H$.
* Equations (7.4.2)–(7.4.4), `ConnGouldToint.Chapter07.isMinOn_weightedTrustRegion_iff_congruence`:
  if $S^T M S = I$, then $Sy$ solves (7.4.1) if and only if $y$ solves the Euclidean ball problem
  with gradient $S^T g$ and Hessian $S^T H S$.
* Theorem 7.4.1, `ConnGouldToint.Chapter07.theorem_7_4_1`: a global minimizer of (7.4.1) satisfies
  $(H + \mu M) s = -g$ with $H + \mu M$ positive semidefinite, $\mu \ge 0$ and
  $\mu (\|s\|_M - \Delta) = 0$, and it is unique if $H + \mu M$ is positive definite.

## Implementation notes

* Vectors are elements of `EuclideanSpace ℝ ι` for a finite index type `ι`, and a matrix acts on
  them through `Matrix.toEuclideanLin`.
* The $M$-inner product space is `Subproblem.ScaledSpace hM`, and `Subproblem.toScaled hM` is the
  identity map into it. The gradient $M^{-1} g$ and the operator $M^{-1} H$ are
  `Subproblem.scaledGrad hM g` and `Subproblem.scaledOp H hM`.

## Deviations from the source

* **Equations (7.4.1)–(7.4.4)** (reading). The norm and feasible set use the total real square
  root, while their minimizer equivalences impose the positive-definite metric or invertible
  congruence. The intrinsic equivalent problem chooses the positive square root for the
  coordinate change. See `ConnGouldToint.Chapter07.isMinOn_weightedTrustRegion_iff_scaled` and
  `ConnGouldToint.Chapter07.isMinOn_weightedTrustRegion_iff_congruence`.
* **Theorem 7.4.1** (generalization). The multiplier statement also gives uniqueness under
  positive definiteness of the shifted Hessian. See `ConnGouldToint.Chapter07.theorem_7_4_1`.
* **Theorem 7.4.1** (correction). The statement requires $\Delta > 0$, as in Section 7.2. At
  $\Delta = 0$ the only feasible point is $0$, and the shifted system has no solution when
  $g \neq 0$. See `ConnGouldToint.Chapter07.theorem_7_4_1`.
-/

open Matrix Metric
open scoped RealInnerProductSpace

namespace ConnGouldToint.Chapter07

open Subproblem

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {H M : Matrix ι ι ℝ} {g : EuclideanSpace ℝ ι} {Δ : ℝ}

/-- **Section 7.4** of [conn2000trust], scaled norm. For a matrix $M \in \mathbb{R}^{n \times n}$,
the **$M$-norm** of $s \in \mathbb{R}^n$ is
$$\|s\|_M = \sqrt{s^T M s}.$$

The square root is `Real.sqrt`, so the value is $0$ when $s^T M s < 0$. The results of this
module assume that $M$ is symmetric positive definite.

**Reading.** Square-root formula defined for unrestricted matrices and zero for a negative quadratic
form.
-/
noncomputable def mNorm (M : Matrix ι ι ℝ) (s : EuclideanSpace ℝ ι) : ℝ :=
  √⟪s, toEuclideanLin M s⟫

/-- **Equation (7.4.1)** of [conn2000trust], objective. For $g \in \mathbb{R}^n$ and
$H \in \mathbb{R}^{n \times n}$, the **quadratic model** is
$$m(s) = g^T s + \tfrac{1}{2} s^T H s.$$
-/
noncomputable def matrixQuadModel (g : EuclideanSpace ℝ ι) (H : Matrix ι ι ℝ)
    (s : EuclideanSpace ℝ ι) : ℝ :=
  ⟪g, s⟫ + (1 / 2) * ⟪s, toEuclideanLin H s⟫

/-- **Equation (7.4.1)** of [conn2000trust], feasible set. For $M \in \mathbb{R}^{n \times n}$ and
$\Delta \in \mathbb{R}$, the **weighted trust region** is the ellipsoid
$\{s \in \mathbb{R}^n : \|s\|_M \le \Delta\}$.

**Reading.** The set uses the total real square-root expression for every real matrix. -/
def weightedTrustRegion (M : Matrix ι ι ℝ) (Δ : ℝ) : Set (EuclideanSpace ℝ ι) :=
  {s | mNorm M s ≤ Δ}

/-- **(7.4.2) derivation** of [conn2000trust].

**Reading.** The metric identity uses the intrinsic positive square root for the change of
coordinates.
-/
private theorem norm_toScaled_eq_mNorm (hM : M.PosDef) (s : EuclideanSpace ℝ ι) :
    ‖toScaled hM s‖ = mNorm M s := by
  rw [norm_toScaled, mNorm, real_inner_comm]

/-- **Equations (7.4.1)–(7.4.4)** of [conn2000trust], intrinsic change of coordinates. Let
$M \in \mathbb{R}^{n \times n}$ be symmetric positive definite, and let $g \in \mathbb{R}^n$,
$H \in \mathbb{R}^{n \times n}$ and $\Delta \in \mathbb{R}$. Equip $\mathbb{R}^n$ with the inner
product $\langle x, y \rangle_M = x^T M y$. Then $s$ minimizes
$m(s) = g^T s + \frac{1}{2} s^T H s$ on $\{s : \|s\|_M \le \Delta\}$ if and only if $s$
minimizes
$$\langle M^{-1} g, s \rangle_M + \tfrac{1}{2} \langle s, M^{-1} H s \rangle_M$$
on the closed ball of radius $\Delta$ of this inner product space.

The inner product space is `Subproblem.ScaledSpace hM`, the identity map into it is
`Subproblem.toScaled hM`, and the model on the right is `Subproblem.quadModel
(Subproblem.scaledGrad hM g) (Subproblem.scaledOp H hM)`. The two models agree pointwise, so no
symmetry of $H$ is needed.

**Reading.** The intrinsic coordinates are chosen by the positive-definite square root. -/
theorem isMinOn_weightedTrustRegion_iff_scaled (hM : M.PosDef) (s : EuclideanSpace ℝ ι) :
    IsMinOn (matrixQuadModel g H) (weightedTrustRegion M Δ) s ↔
      IsMinOn (quadModel (scaledGrad hM g) (scaledOp H hM)) (closedBall 0 Δ)
        (toScaled hM s) := by
  simp only [isMinOn_iff, weightedTrustRegion, Set.mem_ofPred_eq, mem_closedBall_zero_iff]
  constructor
  · intro hs y hy
    obtain ⟨x, rfl⟩ := (toScaled hM).surjective y
    rw [norm_toScaled_eq_mNorm] at hy
    simpa only [matrixQuadModel, quadModel_scaled (hM := hM)] using hs x hy
  · intro hs y hy
    have hy' : ‖toScaled hM y‖ ≤ Δ := by rwa [norm_toScaled_eq_mNorm]
    simpa only [matrixQuadModel, quadModel_scaled (hM := hM)] using hs (toScaled hM y) hy'

/-- **Equations (7.4.2)–(7.4.4)** of [conn2000trust], congruence. Let
$M, S \in \mathbb{R}^{n \times n}$ with $S$ invertible and $S^T M S = I$, and let
$g \in \mathbb{R}^n$, $H \in \mathbb{R}^{n \times n}$ and $\Delta \in \mathbb{R}$. Then for
every $y \in \mathbb{R}^n$, the point $Sy$ minimizes $m(s) = g^T s + \frac{1}{2} s^T H s$ on
$\{s : \|s\|_M \le \Delta\}$ if and only if $y$ minimizes
$$(S^T g)^T y + \tfrac{1}{2} y^T (S^T H S) y$$
on the Euclidean ball $\|y\| \le \Delta$.

Solutions of the two problems correspond by multiplication by $S$. -/
theorem isMinOn_weightedTrustRegion_iff_congruence {S : Matrix ι ι ℝ} (hS : IsUnit S)
    (hcongr : Sᵀ * M * S = 1) (y : EuclideanSpace ℝ ι) :
    IsMinOn (matrixQuadModel g H) (weightedTrustRegion M Δ) (toEuclideanLin S y) ↔
      IsMinOn (matrixQuadModel (toEuclideanLin Sᵀ g) (Sᵀ * H * S)) (closedBall 0 Δ) y := by
  have hnorm (z : EuclideanSpace ℝ ι) : mNorm M (toEuclideanLin S z) = ‖z‖ := by
    rw [mNorm, real_inner_comm, ← inner_toEuclideanLin_conjTranspose_mul_mul_apply,
      conjTranspose_eq_transpose_of_trivial, hcongr, toEuclideanLin_one_apply,
      real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  have hmodel (z : EuclideanSpace ℝ ι) :
      matrixQuadModel (toEuclideanLin Sᵀ g) (Sᵀ * H * S) z =
        matrixQuadModel g H (toEuclideanLin S z) := by
    have hquad : ⟪z, toEuclideanLin (Sᵀ * H * S) z⟫ =
        ⟪toEuclideanLin S z, toEuclideanLin H (toEuclideanLin S z)⟫ := calc
      _ = ⟪toEuclideanLin (Sᵀ * H * S) z, z⟫ := real_inner_comm _ _
      _ = ⟪toEuclideanLin H (toEuclideanLin S z), toEuclideanLin S z⟫ := by
        simpa only [conjTranspose_eq_transpose_of_trivial] using
          inner_toEuclideanLin_conjTranspose_mul_mul_apply H S z
      _ = _ := real_inner_comm _ _
    rw [matrixQuadModel, matrixQuadModel, toEuclideanLin_transpose_inner_left, hquad]
  simp only [isMinOn_iff, weightedTrustRegion, Set.mem_ofPred_eq, mem_closedBall_zero_iff]
  constructor
  · intro hm z hz
    simpa only [hmodel] using hm (toEuclideanLin S z) (by simpa only [hnorm] using hz)
  · intro hm u hu
    let z := toEuclideanLin S⁻¹ u
    have hz : toEuclideanLin S z = u := toEuclideanLin_mul_nonsing_inv_apply hS u
    rw [← hz] at hu ⊢
    rw [hnorm] at hu
    simpa only [hmodel] using hm z hu

/-- **Theorem 7.4.1** of [conn2000trust]. Let $M \in \mathbb{R}^{n \times n}$ be symmetric positive
definite, let $H \in \mathbb{R}^{n \times n}$ be symmetric, let $g \in \mathbb{R}^n$ and
$\Delta > 0$. If $s$ satisfies $\|s\|_M \le \Delta$ and minimizes
$m(s) = g^T s + \frac{1}{2} s^T H s$ on $\{s : \|s\|_M \le \Delta\}$, then there is
$\mu \in \mathbb{R}$ with
$$(H + \mu M) s = -g, \qquad H + \mu M \succeq 0, \qquad \mu \ge 0, \qquad \mu (\|s\|_M -
  \Delta) = 0.$$
If moreover $H + \mu M$ is positive definite, then $s$ is the only minimizer of $m$ on
$\{s : \|s\|_M \le \Delta\}$.

**Correction.** The statement requires $\Delta > 0$, as in Section 7.2. At $\Delta = 0$ the only
feasible point is $s = 0$, and the system $(H + \mu M) 0 = -g$ has no solution when $g \neq 0$.

The proof transports the ball characterization `Subproblem.isMinOn_closedBall_iff` through
`ConnGouldToint.Chapter07.isMinOn_weightedTrustRegion_iff_scaled`.

**Generalization.** The shifted positive-definiteness condition also implies uniqueness. -/
theorem theorem_7_4_1 (hM : M.PosDef) (hH : H.IsHermitian) (hΔ : 0 < Δ)
    {s : EuclideanSpace ℝ ι} (hs : s ∈ weightedTrustRegion M Δ)
    (hmin : IsMinOn (matrixQuadModel g H) (weightedTrustRegion M Δ) s) :
    ∃ μ : ℝ, toEuclideanLin (H + μ • M) s = -g ∧ (H + μ • M).PosSemidef ∧
      0 ≤ μ ∧ μ * (mNorm M s - Δ) = 0 ∧
      ((H + μ • M).PosDef → ∀ u ∈ weightedTrustRegion M Δ,
        IsMinOn (matrixQuadModel g H) (weightedTrustRegion M Δ) u → u = s) := by
  have hsymm := isSymmetric_scaledOp (hM := hM) hH
  have hs' : ‖toScaled hM s‖ ≤ Δ := by rwa [norm_toScaled_eq_mNorm]
  have hm := (isMinOn_weightedTrustRegion_iff_scaled hM s).mp hmin
  obtain ⟨μ, hμ⟩ := (isMinOn_closedBall_iff hsymm hΔ hs').mp hm
  refine ⟨μ, (add_smul_scaledOp_toScaled_eq_neg_iff μ g s).mp hμ.shifted,
    (posSemidef_add_smul_iff_isPositive μ).mpr hμ.isPositive, hμ.nonneg, ?_, ?_⟩
  · simpa only [norm_toScaled_eq_mNorm] using hμ.complementarity
  · intro hpd u hu hminu
    have hc := ((posDef_add_smul_iff_isSymmetricCoercive (hM := hM) μ).mp hpd).isCoercive
    have hu' : ‖toScaled hM u‖ ≤ Δ := by rwa [norm_toScaled_eq_mNorm]
    have hmu := (isMinOn_weightedTrustRegion_iff_scaled hM u).mp hminu
    exact (toScaled hM).injective (eq_of_isMinOn_closedBall_of_posDef hsymm hμ hs' hc hu' hmu)

end ConnGouldToint.Chapter07
