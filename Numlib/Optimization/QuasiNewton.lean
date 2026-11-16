/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Numlib.Analysis.Calculus.MeanValue
import Numlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.Nonlinear.QuasiNewton

/-!
# Secant updates of a Hessian approximation

Let $B \in \mathbb{R}^{n \times n}$ be a symmetric approximation to the Hessian of an objective
function, let $s = x_+ - x$ be the last step, and let $y = \nabla f(x_+) - \nabla f(x)$ be the
corresponding change of the gradient. A secant (quasi-Newton) update produces a new approximation
$B_+$ that satisfies the **secant equation** $B_+ s = y$. This file defines the symmetric secant
updates of Section 7.2.7 of [quarteroni2000numerical], Sections 9.1–9.2 of [dennis1996numerical] and
Section 6.1 of [nocedal2006numerical], and proves the secant equation, the preservation of symmetry,
and the main properties of each update.

The **symmetric rank-one update** (7.43) is the rank-one secant update with the scaling vector
$c = y - Bs$; its inverse is (7.44). The **symmetrization iteration** (7.45) alternates a rank-one
secant update with taking the symmetric part. From a symmetric $B$ it converges to the **general
symmetric update** (7.46). The case $c = s$ of (7.46) is the **Powell-symmetric-Broyden** (PSB)
update, which is the symmetric matrix nearest to $B$ in the Frobenius norm among those that satisfy
the secant equation, and which has bounded deterioration against a Lipschitz Hessian. The
**Davidon–Fletcher–Powell** (DFP) and **Broyden–Fletcher–Goldfarb–Shanno** (BFGS) updates, which
[quarteroni2000numerical] defers to Section 9.2 of [dennis1996numerical], preserve positive
definiteness under the curvature condition $y^T s > 0$.

## Main definitions

* `Matrix.sr1Update`: the symmetric rank-one update (7.43),
  $B_+ = B + (y - Bs)(y - Bs)^T / ((y - Bs)^T s)$.
* `Matrix.symmetrizationStep`: one double step of the symmetrization iteration (7.45).
* `Matrix.generalSymmetricUpdate`: the general symmetric secant update (7.46) with scaling vector
  $c$.
* `Matrix.psbUpdate`: the Powell-symmetric-Broyden update, the case $c = s$ of (7.46).
* `Matrix.bfgsUpdate`: the BFGS update $B_+ = B - (Bs)(Bs)^T / (s^T B s) + y y^T / (y^T s)$.
* `Matrix.dfpUpdate`: the DFP update $B_+ = (I - \rho y s^T) B (I - \rho s y^T) + \rho y y^T$ with
  $\rho = 1 / (y^T s)$.

## Main results

* `Matrix.sr1Update_mulVec`, `Matrix.generalSymmetricUpdate_mulVec`, `Matrix.psbUpdate_mulVec`,
  `Matrix.bfgsUpdate_mulVec`, `Matrix.dfpUpdate_mulVec`: the secant equation $B_+ s = y$ for each
  update.
* `Matrix.sr1Update_inv`: the inverse (7.44) of the symmetric rank-one update.
* `Matrix.tendsto_symmetrizationStep_iterate`: from a symmetric $B$, the symmetrization iteration
  (7.45) converges to (7.46), with the rate $2^{-j}$ of `Matrix.symmetrizationStep_iterate_succ`.
* `Matrix.frobenius_norm_psbUpdate_sub_le`, `Matrix.frobenius_norm_psbUpdate_sub_lt`: the PSB update
  is the unique nearest symmetric matrix to $B$ in the Frobenius norm that satisfies the secant
  equation (Theorem 9.1.1 of [dennis1996numerical]).
* `Matrix.frobenius_norm_psbUpdate_sub_le_add`: bounded deterioration of the PSB update, $\|B_+ -
  H(x_+)\|_F \le \|B - H(x)\|_F + 3 L \|s\|$, the last display of Section 7.2.7 of
  [quarteroni2000numerical].
* `Matrix.bfgsUpdate_posDef`, `Matrix.dfpUpdate_posDef`: the BFGS and DFP updates preserve positive
  definiteness when $y^T s > 0$.

## Implementation notes

* The updates are stated for matrices `Matrix n n ℝ`, not for operators, because every statement is
  about symmetry and the Frobenius norm. The rank-one secant update (7.42) of
  [quarteroni2000numerical] with an arbitrary scaling vector $c$, `Matrix.rankOneSecantUpdate`, and
  Broyden's update `Matrix.broydenUpdate` (the case $c = s$), are in `Numlib.Nonlinear.QuasiNewton`,
  so that the nonsymmetric updates for systems and the symmetric updates for minimization share one
  definition. The operator form of the nonsymmetric update is `Broyden.update`.
* The Frobenius norm is the scoped instance `Matrix.Norms.Frobenius`, opened in the sections that
  use it. The convergence of the symmetrization iteration is stated in the product topology of
  `Matrix n n ℝ`, which every matrix norm induces.
* Divisions follow the Lean convention $x / 0 = 0$, so the updates are total, and the nondegeneracy
  conditions ($c^T s \neq 0$, $s \neq 0$, $y^T s > 0$) appear only in the theorems.
* Two hypotheses that [quarteroni2000numerical] leaves implicit are explicit here. The
  symmetrization iteration (7.45) converges to (7.46) only from a symmetric $B$: one step already
  produces a symmetric matrix, whereas (7.46) with a nonsymmetric $B$ is not symmetric. The bounded
  deterioration estimate also needs a symmetric $B$, because the least-change projection
  $\Delta \mapsto \Delta - (I - P) \Delta (I - P)$, with $P = s s^T / (s^T s)$, is a contraction in
  the Frobenius norm only on symmetric $\Delta$.
-/

open scoped InnerProductSpace
open WithLp Filter Topology

namespace Matrix

variable {n : Type*} [Fintype n]

/-! ### The symmetric rank-one update (7.43) -/

/-- The **symmetric rank-one update**, (7.43) of [quarteroni2000numerical]:
$$B_+ = B + \frac{(y - Bs)(y - Bs)^T}{(y - Bs)^T s}.$$
It is the rank-one secant update `Matrix.rankOneSecantUpdate` with the scaling vector
$c = y - Bs$.

If $(y - Bs)^T s = 0$, the division gives $0$ and $B_+ = B$. -/
noncomputable def sr1Update (B : Matrix n n ℝ) (s y : n → ℝ) : Matrix n n ℝ :=
  rankOneSecantUpdate B s y (y - B *ᵥ s)

/-- The symmetric rank-one update is
$$B_+ = B + \frac{1}{(y - Bs)^T s} (y - Bs)(y - Bs)^T.$$
-/
theorem sr1Update_eq (B : Matrix n n ℝ) (s y : n → ℝ) :
    sr1Update B s y
      = B + (1 / ((y - B *ᵥ s) ⬝ᵥ s)) • vecMulVec (y - B *ᵥ s) (y - B *ᵥ s) :=
  rfl

/-- If $B$ is symmetric, then the symmetric rank-one update $B_+$ is symmetric. -/
theorem sr1Update_isSymm {B : Matrix n n ℝ} (hB : B.IsSymm) (s y : n → ℝ) :
    (sr1Update B s y).IsSymm :=
  hB.add (IsSymm.smul (transpose_vecMulVec (y - B *ᵥ s) (y - B *ᵥ s)) _)

/-- **The secant equation** for the symmetric rank-one update: if $(y - Bs)^T s \neq 0$, then
$B_+ s = y$. -/
theorem sr1Update_mulVec (B : Matrix n n ℝ) {s y : n → ℝ} (h : (y - B *ᵥ s) ⬝ᵥ s ≠ 0) :
    sr1Update B s y *ᵥ s = y :=
  rankOneSecantUpdate_mulVec B h y

section Inverse

variable [DecidableEq n]

/-- For a symmetric invertible $B$, $(Bs)^T (B^{-1} y) = y^T s$. -/
private theorem mulVec_dotProduct_inv_mulVec {B : Matrix n n ℝ} (hB : B.IsSymm) (hu : IsUnit B)
    (s y : n → ℝ) : (B *ᵥ s) ⬝ᵥ (B⁻¹ *ᵥ y) = y ⬝ᵥ s := by
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hB.eq,
    mulVec_nonsing_inv_mulVec hu]

/-- **The inverse of the symmetric rank-one update**, (7.44) of [quarteroni2000numerical]. Let $B$
be symmetric and invertible, and let $C = B^{-1}$. If $(y - Bs)^T s \neq 0$ and
$(s - Cy)^T y \neq 0$, then
$$B_+^{-1} = C + \frac{(s - Cy)(s - Cy)^T}{(s - Cy)^T y}.$$
Thus the inverse approximation can be updated directly.

The proof applies the Sherman–Morrison formula `Matrix.inv_add_vecMulVec` with
$u = (y - Bs) / ((y - Bs)^T s)$ and $v = y - Bs$. It uses $C(y - Bs) = -(s - Cy)$ and $(y -
Bs)^T (s - Cy) = (y - Bs)^T s + (s - Cy)^T y$. -/
theorem sr1Update_inv {B : Matrix n n ℝ} (hB : B.IsSymm) (hu : IsUnit B) {s y : n → ℝ}
    (hσ : (y - B *ᵥ s) ⬝ᵥ s ≠ 0) (hw : (s - B⁻¹ *ᵥ y) ⬝ᵥ y ≠ 0) :
    (sr1Update B s y)⁻¹
      = B⁻¹ + (1 / ((s - B⁻¹ *ᵥ y) ⬝ᵥ y)) • vecMulVec (s - B⁻¹ *ᵥ y) (s - B⁻¹ *ᵥ y) := by
  set C : Matrix n n ℝ := B⁻¹ with hC
  set r : n → ℝ := y - B *ᵥ s with hr
  set w : n → ℝ := s - C *ᵥ y with hwdef
  set σ : ℝ := r ⬝ᵥ s with hσdef
  have hCr : C *ᵥ r = -w := by
    rw [hr, hwdef, mulVec_sub, hC, nonsing_inv_mulVec_mulVec hu, neg_sub]
  have hCt : Cᵀ = C := by rw [hC, transpose_nonsing_inv, hB.eq]
  have hrC : r ᵥ* C = -w := by rw [← hCt, vecMul_transpose, hCr]
  have hrw : r ⬝ᵥ w = σ + w ⬝ᵥ y := by
    simp only [hr, hwdef, hσdef, sub_dotProduct, dotProduct_sub]
    rw [mulVec_dotProduct_inv_mulVec hB hu, dotProduct_comm (B *ᵥ s) s,
      dotProduct_comm (C *ᵥ y) y, dotProduct_comm s y]
    ring
  have hden' : 1 + r ⬝ᵥ (C *ᵥ ((1 / σ) • r)) = -(w ⬝ᵥ y) / σ := by
    rw [mulVec_smul, hCr, smul_neg, dotProduct_neg, dotProduct_smul, hrw, smul_eq_mul]
    field_simp
    ring
  have hden : 1 + r ⬝ᵥ (C *ᵥ ((1 / σ) • r)) ≠ 0 := by
    rw [hden']
    exact div_ne_zero (neg_ne_zero.2 hw) hσ
  rw [sr1Update_eq, ← hr, ← hσdef, ← smul_vecMulVec, inv_add_vecMulVec hu hden, ← hC, hrC, hden',
    mulVec_smul, hCr, smul_neg, neg_vecMulVec, vecMulVec_neg, neg_neg, smul_vecMulVec, smul_smul,
    sub_eq_add_neg, ← neg_smul]
  congr 2
  field_simp

end Inverse

/-! ### The symmetrization iteration (7.45) and its limit (7.46) -/

/-- **One double step of the symmetrization iteration**, (7.45) of [quarteroni2000numerical]. It is
the rank-one secant update with scaling vector $c$,
$$B^{(2j+1)} = B^{(2j)} + \frac{(y - B^{(2j)} s) c^T}{c^T s},$$
followed by the symmetric part $B^{(2j+2)} = \frac{1}{2} \bigl(B^{(2j+1)} +
(B^{(2j+1)})^T\bigr)$.

The iterates are $B^{(2j)} = T^j B$, where $T$ is `Matrix.symmetrizationStep s y c`. -/
noncomputable def symmetrizationStep (s y c : n → ℝ) (B : Matrix n n ℝ) : Matrix n n ℝ :=
  (1 / 2 : ℝ) • (rankOneSecantUpdate B s y c + (rankOneSecantUpdate B s y c)ᵀ)

/-- **The general symmetric secant update**, (7.46) of [quarteroni2000numerical], with scaling
vector $c$:
$$B_+ = B + \frac{(y - Bs) c^T + c (y - Bs)^T}{c^T s} - \frac{(y - Bs)^T s}{(c^T s)^2} c c^T.$$
From a symmetric $B$ it is the limit of the symmetrization iteration
(`Matrix.tendsto_symmetrizationStep_iterate`). With $c = s$ it is the Powell-symmetric-Broyden
update `Matrix.psbUpdate`.

If $c^T s = 0$, the divisions give $0$ and $B_+ = B$. -/
noncomputable def generalSymmetricUpdate (B : Matrix n n ℝ) (s y c : n → ℝ) : Matrix n n ℝ :=
  B + (1 / (c ⬝ᵥ s)) • (vecMulVec (y - B *ᵥ s) c + vecMulVec c (y - B *ᵥ s))
    - (((y - B *ᵥ s) ⬝ᵥ s) / (c ⬝ᵥ s) ^ 2) • vecMulVec c c

/-- If $B$ is symmetric, then the general symmetric update (7.46) is symmetric for every $s$, $y$
and $c$. -/
theorem generalSymmetricUpdate_isSymm {B : Matrix n n ℝ} (hB : B.IsSymm) (s y c : n → ℝ) :
    (generalSymmetricUpdate B s y c).IsSymm := by
  unfold IsSymm generalSymmetricUpdate
  rw [transpose_sub, transpose_add, transpose_smul, transpose_add, transpose_vecMulVec,
    transpose_vecMulVec, transpose_smul, transpose_vecMulVec, hB.eq, add_comm (vecMulVec c _)]

/-- **The secant equation** for the general symmetric update (7.46): if $c^T s \neq 0$, then
$B_+ s = y$. -/
theorem generalSymmetricUpdate_mulVec (B : Matrix n n ℝ) {s c : n → ℝ} (hcs : c ⬝ᵥ s ≠ 0)
    (y : n → ℝ) : generalSymmetricUpdate B s y c *ᵥ s = y := by
  simp only [generalSymmetricUpdate, sub_mulVec, add_mulVec, smul_mulVec, vecMulVec_mulVec,
    op_smul_eq_smul, smul_add, smul_smul]
  rw [one_div_mul_cancel hcs, one_smul,
    show (y - B *ᵥ s) ⬝ᵥ s / (c ⬝ᵥ s) ^ 2 * (c ⬝ᵥ s) = 1 / (c ⬝ᵥ s) * ((y - B *ᵥ s) ⬝ᵥ s) by
      field_simp]
  abel

/-- **The Powell-symmetric-Broyden update**, (7.46) of [quarteroni2000numerical] with $c = s$:
$$B_+ = B + \frac{(y - Bs) s^T + s (y - Bs)^T}{s^T s} - \frac{(y - Bs)^T s}{(s^T s)^2} s s^T.$$
-/
noncomputable def psbUpdate (B : Matrix n n ℝ) (s y : n → ℝ) : Matrix n n ℝ :=
  generalSymmetricUpdate B s y s

/-- The Powell-symmetric-Broyden update is
$$B_+ = B + \frac{1}{s^T s} \bigl((y - Bs) s^T + s (y - Bs)^T\bigr) - \frac{(y - Bs)^T s}{(s^T
  s)^2} s s^T.$$
-/
theorem psbUpdate_eq (B : Matrix n n ℝ) (s y : n → ℝ) :
    psbUpdate B s y
      = B + (1 / (s ⬝ᵥ s)) • (vecMulVec (y - B *ᵥ s) s + vecMulVec s (y - B *ᵥ s))
        - (((y - B *ᵥ s) ⬝ᵥ s) / (s ⬝ᵥ s) ^ 2) • vecMulVec s s :=
  rfl

/-- If $B$ is symmetric, then the Powell-symmetric-Broyden update is symmetric. -/
theorem psbUpdate_isSymm {B : Matrix n n ℝ} (hB : B.IsSymm) (s y : n → ℝ) :
    (psbUpdate B s y).IsSymm :=
  generalSymmetricUpdate_isSymm hB s y s

/-- **The secant equation** for the Powell-symmetric-Broyden update: if $s \neq 0$, then
$B_+ s = y$. -/
theorem psbUpdate_mulVec (B : Matrix n n ℝ) {s : n → ℝ} (hs : s ≠ 0) (y : n → ℝ) :
    psbUpdate B s y *ᵥ s = y :=
  generalSymmetricUpdate_mulVec B (mt dotProduct_self_eq_zero.1 hs) y

section Symmetrization

variable {s y c : n → ℝ}

/-- One symmetrization step from a perturbation of a symmetric matrix. Let $M$ be symmetric with
$Ms = y$, and let $\Delta$ be symmetric. Then the symmetrization step $T$ satisfies
$$T(M + \Delta) = M + \Delta - \frac{(\Delta s) c^T + c (\Delta s)^T}{2 c^T s}.$$
-/
theorem symmetrizationStep_add_of_isSymm {M Δ : Matrix n n ℝ} (hM : M.IsSymm) (hMs : M *ᵥ s = y)
    (hΔ : Δ.IsSymm) :
    symmetrizationStep s y c (M + Δ)
      = M + Δ - (1 / (2 * (c ⬝ᵥ s))) • (vecMulVec (Δ *ᵥ s) c + vecMulVec c (Δ *ᵥ s)) := by
  have h1 : rankOneSecantUpdate (M + Δ) s y c
      = M + Δ - (1 / (c ⬝ᵥ s)) • vecMulVec (Δ *ᵥ s) c := by
    rw [rankOneSecantUpdate, add_mulVec, hMs, sub_add_cancel_left, neg_vecMulVec, smul_neg,
      ← sub_eq_add_neg]
  rw [symmetrizationStep, h1, transpose_sub, transpose_add, transpose_smul, transpose_vecMulVec,
    hM.eq, hΔ.eq]
  module

/-- The first symmetrization step from a symmetric $B$:
$$T B = B + \frac{(y - Bs) c^T + c (y - Bs)^T}{2 c^T s}.$$
-/
theorem symmetrizationStep_of_isSymm {B : Matrix n n ℝ} (hB : B.IsSymm) :
    symmetrizationStep s y c B
      = B + (1 / (2 * (c ⬝ᵥ s))) • (vecMulVec (y - B *ᵥ s) c + vecMulVec c (y - B *ᵥ s)) := by
  rw [symmetrizationStep, rankOneSecantUpdate, transpose_add, transpose_smul, transpose_vecMulVec,
    hB.eq]
  module

/-- Let $c^T s \neq 0$ and let $B$ be symmetric. Let $\bar B$ be the general symmetric update (7.46)
and let $\Delta_1 = T B - \bar B$ be the deviation of the first symmetrization step from it.
Then
$$\frac{(\Delta_1 s) c^T + c (\Delta_1 s)^T}{c^T s} = \Delta_1,$$
so the linear part of $T$ halves $\Delta_1$.

This identity is the whole content of the convergence of the symmetrization iteration. -/
theorem symmetrizationStep_sub_generalSymmetricUpdate_key (hcs : c ⬝ᵥ s ≠ 0)
    {B : Matrix n n ℝ} (hB : B.IsSymm) :
    (1 / (c ⬝ᵥ s)) • (vecMulVec ((symmetrizationStep s y c B - generalSymmetricUpdate B s y c)
        *ᵥ s) c
      + vecMulVec c ((symmetrizationStep s y c B - generalSymmetricUpdate B s y c) *ᵥ s))
      = symmetrizationStep s y c B - generalSymmetricUpdate B s y c := by
  set r : n → ℝ := y - B *ᵥ s with hr
  set σ : ℝ := c ⬝ᵥ s with hσ
  set ρ : ℝ := r ⬝ᵥ s with hρ
  have hΔ : symmetrizationStep s y c B - generalSymmetricUpdate B s y c
      = (-(1 / (2 * σ))) • (vecMulVec r c + vecMulVec c r) + (ρ / σ ^ 2) • vecMulVec c c := by
    rw [symmetrizationStep_of_isSymm hB, generalSymmetricUpdate]
    module
  have hΔs : (symmetrizationStep s y c B - generalSymmetricUpdate B s y c) *ᵥ s
      = (-(1 / 2 : ℝ)) • r + (ρ / (2 * σ)) • c := by
    rw [hΔ]
    simp only [add_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul,
      smul_add, smul_smul, ← hσ, ← hρ]
    rw [show -(1 / (2 * σ)) * σ = -(1 / 2 : ℝ) by field_simp,
      show ρ / σ ^ 2 * σ = ρ / σ by field_simp,
      show -(1 / (2 * σ)) * ρ = -(ρ / (2 * σ)) by ring]
    module
  rw [hΔs]
  conv_rhs => rw [hΔ]
  simp only [add_vecMulVec, vecMulVec_add, smul_vecMulVec, vecMulVec_smul]
  module

/-- **The closed form of the symmetrization iteration.** Let $c^T s \neq 0$ and let $B$ be
symmetric. Let $T$ be the symmetrization step and $\bar B$ the general symmetric update (7.46).
Then for every $j \ge 0$,
$$T^{j+1} B = \bar B + 2^{-j} (T B - \bar B).$$

The limit $\bar B$ is a fixed point of $T$, because it is symmetric and satisfies the secant
equation. The map $T$ is affine, and its linear part halves the deviation $T B - \bar B$. -/
theorem symmetrizationStep_iterate_succ (hcs : c ⬝ᵥ s ≠ 0) {B : Matrix n n ℝ} (hB : B.IsSymm)
    (j : ℕ) :
    (symmetrizationStep s y c)^[j + 1] B
      = generalSymmetricUpdate B s y c
        + ((1 / 2 : ℝ) ^ j) • (symmetrizationStep s y c B - generalSymmetricUpdate B s y c) := by
  set B' : Matrix n n ℝ := generalSymmetricUpdate B s y c with hB'
  set Δ : Matrix n n ℝ := symmetrizationStep s y c B - B' with hΔ
  have hB's : B' *ᵥ s = y := generalSymmetricUpdate_mulVec B hcs y
  have hB'sym : B'.IsSymm := generalSymmetricUpdate_isSymm hB s y c
  have hΔsym : Δ.IsSymm := by
    refine IsSymm.sub ?_ hB'sym
    rw [symmetrizationStep_of_isSymm hB]
    refine hB.add (IsSymm.smul ?_ _)
    unfold IsSymm
    rw [transpose_add, transpose_vecMulVec, transpose_vecMulVec, add_comm]
  have hkey := symmetrizationStep_sub_generalSymmetricUpdate_key (y := y) hcs hB
  rw [← hB', ← hΔ] at hkey
  induction j with
  | zero =>
    rw [zero_add, Function.iterate_one, pow_zero, one_smul, hΔ, add_sub_cancel]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, symmetrizationStep_add_of_isSymm hB'sym hB's
      (hΔsym.smul _), smul_mulVec, vecMulVec_smul, smul_vecMulVec, ← smul_add, smul_smul,
      show 1 / (2 * (c ⬝ᵥ s)) * (1 / 2 : ℝ) ^ j = (1 / 2 : ℝ) ^ j * (1 / 2) * (1 / (c ⬝ᵥ s)) by
        ring,
      mul_smul, mul_smul, hkey, pow_succ, mul_smul]
    module

/-- **The symmetrization iteration converges to the general symmetric update**, (7.45)–(7.46) of
[quarteroni2000numerical]; see also Section 9.1 of [dennis1996numerical] and Powell (1970). Let
$c^T s \neq 0$ and let $B$ be symmetric. Then
$$T^j B \to \bar B \quad \text{as } j \to \infty,$$
where $T$ is the symmetrization step and $\bar B$ is the general symmetric update (7.46). The
rate is geometric with ratio $1/2$, by `Matrix.symmetrizationStep_iterate_succ`.

The source states the limit without proof and without the symmetry of $B$. The symmetry is
needed: the first step is symmetric for every $B$, but (7.46) is symmetric only when $B$ is. The
convergence is in the product topology of `Matrix n n ℝ`. -/
theorem tendsto_symmetrizationStep_iterate (hcs : c ⬝ᵥ s ≠ 0) {B : Matrix n n ℝ}
    (hB : B.IsSymm) :
    Tendsto (fun j => (symmetrizationStep s y c)^[j] B) atTop
      (𝓝 (generalSymmetricUpdate B s y c)) := by
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  simp only [symmetrizationStep_iterate_succ hcs hB]
  have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)).smul_const (symmetrizationStep s y c B - generalSymmetricUpdate B s y c))
  simpa using tendsto_const_nhds.add h

end Symmetrization

/-! ### Least change in the Frobenius norm -/

section Frobenius

open scoped Matrix.Norms.Frobenius

variable [DecidableEq n]

/-- **Pythagoras for the two-sided compression by a symmetric idempotent.** Let $Q^T = Q$ and
$Q^2 = Q$. Then for every $A$,
$$\|A - QAQ\|_F^2 + \|QAQ\|_F^2 = \|A\|_F^2.$$

The matrix $QAQ$ is the Frobenius-orthogonal projection of $A$ onto $\{QZQ\}$. In the trace form
$\|M\|_F^2 = \operatorname{tr}(M^T M)$, the cross terms are $\operatorname{tr}(A^T QAQ) =
\operatorname{tr}((QAQ)^T (QAQ))$, by cyclicity and $Q^2 = Q$. -/
theorem frobenius_norm_sq_sub_mul_mul_add_sq (A : Matrix n n ℝ) {Q : Matrix n n ℝ}
    (hQt : Qᵀ = Q) (hQQ : Q * Q = Q) :
    ‖A - Q * A * Q‖ ^ 2 + ‖Q * A * Q‖ ^ 2 = ‖A‖ ^ 2 := by
  set N : Matrix n n ℝ := Q * A * Q with hN
  have hNt : Nᵀ = Q * Aᵀ * Q := by
    rw [hN, transpose_mul, transpose_mul, hQt, Matrix.mul_assoc]
  have hNN : trace (Nᵀ * N) = trace (Aᵀ * N) := by
    rw [hNt, hN]
    calc trace (Q * Aᵀ * Q * (Q * A * Q))
        = trace (Q * (Aᵀ * Q * (Q * A * Q))) := by simp only [Matrix.mul_assoc]
      _ = trace (Aᵀ * Q * (Q * A * Q) * Q) := trace_mul_comm _ _
      _ = trace (Aᵀ * (Q * Q) * A * (Q * Q)) := by simp only [Matrix.mul_assoc]
      _ = trace (Aᵀ * (Q * A * Q)) := by rw [hQQ]; simp only [Matrix.mul_assoc]
  have hNA : trace (Nᵀ * A) = trace (Aᵀ * N) := by
    rw [← trace_transpose, transpose_mul, transpose_transpose]
  rw [frobenius_norm_sq_eq_trace_transpose, frobenius_norm_sq_eq_trace_transpose,
    frobenius_norm_sq_eq_trace_transpose, transpose_sub, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.mul_sub]
  simp only [trace_sub, hNN, hNA]
  ring

/-- **The complement of a two-sided compression by a symmetric idempotent has no larger Frobenius
norm.** If $Q^T = Q$ and $Q^2 = Q$, then $\|A - QAQ\|_F \le \|A\|_F$ for every $A$. -/
theorem frobenius_norm_sub_mul_mul_le (A : Matrix n n ℝ) {Q : Matrix n n ℝ} (hQt : Qᵀ = Q)
    (hQQ : Q * Q = Q) : ‖A - Q * A * Q‖ ≤ ‖A‖ := by
  have h := frobenius_norm_sq_sub_mul_mul_add_sq A hQt hQQ
  exact le_of_sq_le_sq (by nlinarith [sq_nonneg ‖Q * A * Q‖]) (norm_nonneg _)

variable {s : n → ℝ}

omit [DecidableEq n] in
/-- The orthogonal projector $P = s s^T / (s^T s)$ onto the span of $s$ is symmetric. -/
private theorem transpose_proj (s : n → ℝ) :
    ((1 / (s ⬝ᵥ s)) • vecMulVec s s)ᵀ = (1 / (s ⬝ᵥ s)) • vecMulVec s s := by
  rw [transpose_smul, transpose_vecMulVec]

omit [DecidableEq n] in
/-- If $s \neq 0$, the orthogonal projector $P = s s^T / (s^T s)$ is idempotent. -/
private theorem proj_mul_proj (hs : s ≠ 0) :
    (1 / (s ⬝ᵥ s)) • vecMulVec s s * ((1 / (s ⬝ᵥ s)) • vecMulVec s s)
      = (1 / (s ⬝ᵥ s)) • vecMulVec s s := by
  have hss : s ⬝ᵥ s ≠ 0 := mt dotProduct_self_eq_zero.1 hs
  rw [Matrix.smul_mul, Matrix.mul_smul, vecMulVec_mul_vecMulVec, vecMulVec_smul, smul_smul,
    smul_smul]
  congr 1
  field_simp

/-- **The PSB correction is the least-change projection.** Let $\Delta$ be symmetric with
$\Delta s = y - Bs$, and let $P = s s^T / (s^T s)$. Then the Powell-symmetric-Broyden update
$B_+$ satisfies
$$B_+ - B = \Delta - (I - P) \Delta (I - P).$$
Thus the update moves $B$ by the component of $\Delta$ outside the subspace
$\{(I - P) Z (I - P)\}$ of symmetric matrices that vanish on $s$. -/
theorem psbUpdate_sub_eq_of_isSymm {B Δ : Matrix n n ℝ} (hΔ : Δ.IsSymm) {y : n → ℝ}
    (hΔs : Δ *ᵥ s = y - B *ᵥ s) :
    psbUpdate B s y - B
      = Δ - (1 - (1 / (s ⬝ᵥ s)) • vecMulVec s s) * Δ * (1 - (1 / (s ⬝ᵥ s)) • vecMulVec s s) := by
  have hsΔ : s ᵥ* Δ = y - B *ᵥ s := by rw [← mulVec_transpose, hΔ.eq, hΔs]
  have hE : psbUpdate B s y - B
      = (1 / (s ⬝ᵥ s)) • (vecMulVec (y - B *ᵥ s) s + vecMulVec s (y - B *ᵥ s))
        - (((y - B *ᵥ s) ⬝ᵥ s) / (s ⬝ᵥ s) ^ 2) • vecMulVec s s := by
    rw [psbUpdate_eq]
    abel
  rw [hE]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, mul_vecMulVec, vecMulVec_mul, hΔs, hsΔ, sub_mulVec, smul_mulVec,
    vecMulVec_mulVec, op_smul_eq_smul, sub_vecMulVec, smul_vecMulVec, smul_smul]
  module

/-- **Least change of the Powell-symmetric-Broyden update in the Frobenius norm**, Theorem 9.1.1 of
[dennis1996numerical] and the characterization stated after (7.46) in [quarteroni2000numerical].
Let $B$ be symmetric and $s \neq 0$, and let $B'$ be any symmetric matrix with $B' s = y$. Then
the PSB update $B_+$ satisfies
$$\|B_+ - B\|_F \le \|B' - B\|_F.$$

With $\Delta = B' - B$ the correction is $\Delta - (I - P) \Delta (I - P)$, the complement of a
two-sided compression by the symmetric idempotent $I - P$. Hence it is no longer than $\Delta$,
by `Matrix.frobenius_norm_sub_mul_mul_le`. -/
theorem frobenius_norm_psbUpdate_sub_le {B B' : Matrix n n ℝ} (hB : B.IsSymm) (hs : s ≠ 0)
    {y : n → ℝ} (hB' : B'.IsSymm) (hB's : B' *ᵥ s = y) :
    ‖psbUpdate B s y - B‖ ≤ ‖B' - B‖ := by
  have hΔ : (B' - B).IsSymm := hB'.sub hB
  have hΔs : (B' - B) *ᵥ s = y - B *ᵥ s := by rw [sub_mulVec, hB's]
  rw [psbUpdate_sub_eq_of_isSymm hΔ hΔs]
  exact frobenius_norm_sub_mul_mul_le _ (by rw [transpose_sub, transpose_one, transpose_proj])
    (by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul,
        Matrix.mul_one, proj_mul_proj hs]
      abel)

/-- **Uniqueness in the least-change characterization.** Let $B$ be symmetric and $s \neq 0$, and
let $B'$ be a symmetric matrix with $B' s = y$ and $B' \neq B_+$, where $B_+$ is the
Powell-symmetric-Broyden update. Then
$$\|B_+ - B\|_F < \|B' - B\|_F.$$
Thus the PSB update is the unique solution of the minimization problem stated after (7.46) in
[quarteroni2000numerical]. -/
theorem frobenius_norm_psbUpdate_sub_lt {B B' : Matrix n n ℝ} (hB : B.IsSymm) (hs : s ≠ 0)
    {y : n → ℝ} (hB' : B'.IsSymm) (hB's : B' *ᵥ s = y) (hne : B' ≠ psbUpdate B s y) :
    ‖psbUpdate B s y - B‖ < ‖B' - B‖ := by
  have hΔ : (B' - B).IsSymm := hB'.sub hB
  have hΔs : (B' - B) *ᵥ s = y - B *ᵥ s := by rw [sub_mulVec, hB's]
  set Q : Matrix n n ℝ := 1 - (1 / (s ⬝ᵥ s)) • vecMulVec s s with hQ
  have hQt : Qᵀ = Q := by rw [hQ, transpose_sub, transpose_one, transpose_proj]
  have hQQ : Q * Q = Q := by
    rw [hQ, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul,
      Matrix.mul_one, proj_mul_proj hs]
    abel
  have hE := psbUpdate_sub_eq_of_isSymm hΔ hΔs
  rw [← hQ] at hE
  have hpyth := frobenius_norm_sq_sub_mul_mul_add_sq (B' - B) hQt hQQ
  have hN : Q * (B' - B) * Q ≠ 0 := by
    intro h0
    apply hne
    rw [h0, sub_zero] at hE
    exact (sub_left_inj.1 hE).symm
  have hNpos : 0 < ‖Q * (B' - B) * Q‖ := norm_pos_iff.2 hN
  rw [hE]
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) (by nlinarith)

/-- The linear part of the PSB correction: the map $r \mapsto (r s^T + s r^T) / (s^T s) - ((r^T s) /
(s^T s)^2) s s^T$, whose value at $r = y - Bs$ is $B_+ - B$. -/
private noncomputable def psbCorrection (s r : n → ℝ) : Matrix n n ℝ :=
  (1 / (s ⬝ᵥ s)) • (vecMulVec r s + vecMulVec s r) - ((r ⬝ᵥ s) / (s ⬝ᵥ s) ^ 2) • vecMulVec s s

omit [DecidableEq n] in
private theorem psbCorrection_sub (s r₁ r₂ : n → ℝ) :
    psbCorrection s (r₁ - r₂) = psbCorrection s r₁ - psbCorrection s r₂ := by
  simp only [psbCorrection, sub_vecMulVec, vecMulVec_sub, sub_dotProduct]
  module

omit [DecidableEq n] in
private theorem psbUpdate_sub_eq_psbCorrection (B : Matrix n n ℝ) (s y : n → ℝ) :
    psbUpdate B s y - B = psbCorrection s (y - B *ᵥ s) := by
  rw [psbUpdate_eq, psbCorrection]
  abel

/-- If $s \neq 0$, the Frobenius norm of the PSB correction at $r$ is at most $3 \|r\| / \|s\|$. -/
private theorem frobenius_norm_psbCorrection_le (hs : s ≠ 0) (r : n → ℝ) :
    ‖psbCorrection s r‖ ≤ 3 * ‖toLp 2 r‖ / ‖toLp 2 s‖ := by
  have hs0 : 0 < ‖toLp 2 s‖ := norm_pos_iff.2 (by simpa using hs)
  have hrs : |r ⬝ᵥ s| ≤ ‖toLp 2 r‖ * ‖toLp 2 s‖ := by
    have h := abs_real_inner_le_norm (toLp 2 r) (toLp 2 s)
    rwa [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm] at h
  have h1 : ‖(1 / (s ⬝ᵥ s)) • (vecMulVec r s + vecMulVec s r)‖
      ≤ 2 * ‖toLp 2 r‖ / ‖toLp 2 s‖ := by
    rw [norm_smul, Real.norm_eq_abs, dotProduct_self_eq_norm_sq, abs_of_nonneg (by positivity)]
    calc 1 / ‖toLp 2 s‖ ^ 2 * ‖vecMulVec r s + vecMulVec s r‖
        ≤ 1 / ‖toLp 2 s‖ ^ 2 * (‖toLp 2 r‖ * ‖toLp 2 s‖ + ‖toLp 2 s‖ * ‖toLp 2 r‖) := by
          gcongr
          exact (norm_add_le _ _).trans
            (add_le_add (frobenius_norm_vecMulVec_le _ _) (frobenius_norm_vecMulVec_le _ _))
      _ = 2 * ‖toLp 2 r‖ / ‖toLp 2 s‖ := by field_simp; ring
  have h2 : ‖((r ⬝ᵥ s) / (s ⬝ᵥ s) ^ 2) • vecMulVec s s‖ ≤ ‖toLp 2 r‖ / ‖toLp 2 s‖ := by
    rw [norm_smul, Real.norm_eq_abs, dotProduct_self_eq_norm_sq, abs_div, abs_of_nonneg
      (by positivity : (0 : ℝ) ≤ (‖toLp 2 s‖ ^ 2) ^ 2)]
    calc |r ⬝ᵥ s| / (‖toLp 2 s‖ ^ 2) ^ 2 * ‖vecMulVec s s‖
        ≤ ‖toLp 2 r‖ * ‖toLp 2 s‖ / (‖toLp 2 s‖ ^ 2) ^ 2 * (‖toLp 2 s‖ * ‖toLp 2 s‖) := by
          gcongr
          exact frobenius_norm_vecMulVec_le _ _
      _ = ‖toLp 2 r‖ / ‖toLp 2 s‖ := by field_simp
  calc ‖psbCorrection s r‖
      ≤ ‖(1 / (s ⬝ᵥ s)) • (vecMulVec r s + vecMulVec s r)‖
        + ‖((r ⬝ᵥ s) / (s ⬝ᵥ s) ^ 2) • vecMulVec s s‖ := norm_sub_le _ _
    _ ≤ 2 * ‖toLp 2 r‖ / ‖toLp 2 s‖ + ‖toLp 2 r‖ / ‖toLp 2 s‖ := add_le_add h1 h2
    _ = 3 * ‖toLp 2 r‖ / ‖toLp 2 s‖ := by ring

/-- **Bounded deterioration of the Powell-symmetric-Broyden update**, the last display of Section
7.2.7 of [quarteroni2000numerical]; see also Section 9.1 of [dennis1996numerical]. Let
$D \subseteq \mathbb{R}^n$ be convex, and let $g : \mathbb{R}^n \to \mathbb{R}^n$ have at every
$w \in D$ the derivative $H(w)$, a symmetric matrix. Let $H$ be $L$-Lipschitz on $D$ from the
Euclidean norm to the Frobenius norm. Let $x \in D$, $s \neq 0$ and $x_+ = x + s \in D$, let
$y = g(x_+) - g(x)$, and let $B$ be symmetric. Then the PSB update $B_+$ satisfies
$$\|B_+ - H(x_+)\|_F \le \|B - H(x)\|_F + 3 L \|s\|.$$

The correction is linear in the secant residual $y - Bs = (y - H(x_+) s) - (B - H(x_+)) s$. Its
value at $-(B - H(x_+)) s$ combines with $B - H(x_+)$ into the compression
$(I - P)(B - H(x_+))(I - P)$, of norm at most $\|B - H(x_+)\|_F \le \|B - H(x)\|_F + L \|s\|$.
Its value at $y - H(x_+) s$ has norm at most $3 \|y - H(x_+) s\| / \|s\| \le \frac{3}{2} L
\|s\|$, by the mean value inequality `Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le`.
The proof gives the constant $5/2$; the statement keeps the constant $3$ of the source.

The space $\mathbb{R}^n$ is `EuclideanSpace ℝ n`, and the derivative of $g$ at $w$ is
`toEuclideanCLM (H w)`. -/
theorem frobenius_norm_psbUpdate_sub_le_add {g : EuclideanSpace ℝ n → EuclideanSpace ℝ n}
    {H : EuclideanSpace ℝ n → Matrix n n ℝ} {D : Set (EuclideanSpace ℝ n)} (hD : Convex ℝ D)
    (hg : ∀ w ∈ D, HasFDerivAt g (toEuclideanCLM (𝕜 := ℝ) (H w)) w)
    (hH : ∀ w ∈ D, (H w).IsSymm) {L : ℝ} (hL : ∀ w ∈ D, ∀ z ∈ D, ‖H w - H z‖ ≤ L * ‖w - z‖)
    {x : EuclideanSpace ℝ n} (hx : x ∈ D) (hs : s ≠ 0) (hxs : x + toLp 2 s ∈ D)
    {B : Matrix n n ℝ} (hB : B.IsSymm) :
    ‖psbUpdate B s (ofLp (g (x + toLp 2 s) - g x)) - H (x + toLp 2 s)‖
      ≤ ‖B - H x‖ + 3 * L * ‖toLp 2 s‖ := by
  set xp : EuclideanSpace ℝ n := x + toLp 2 s with hxp
  set y : n → ℝ := ofLp (g xp - g x) with hy
  set w : n → ℝ := y - H xp *ᵥ s with hw
  set Δ : Matrix n n ℝ := B - H xp with hΔ
  set Q : Matrix n n ℝ := 1 - (1 / (s ⬝ᵥ s)) • vecMulVec s s with hQ
  have hs0 : 0 < ‖toLp 2 s‖ := norm_pos_iff.2 (by simpa using hs)
  have hsn : ‖xp - x‖ = ‖toLp 2 s‖ := by rw [hxp, add_sub_cancel_left]
  -- `L ≥ 0`
  have hL0 : 0 ≤ L := by
    have h := hL _ hxs _ hx
    rw [hsn] at h
    exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans h) hs0
  -- the decomposition of the error
  have hΔsym : Δ.IsSymm := hB.sub (hH _ hxs)
  have hdecomp : psbUpdate B s y - H xp = Q * Δ * Q + psbCorrection s w := by
    have h1 : psbUpdate B s y - H xp = Δ + (psbUpdate B s y - B) := by rw [hΔ]; abel
    have h2 : y - B *ᵥ s = w - Δ *ᵥ s := by rw [hw, hΔ, sub_mulVec]; abel
    have h3 : psbCorrection s (Δ *ᵥ s) = Δ - Q * Δ * Q := by
      have := psbUpdate_sub_eq_of_isSymm (B := H xp) (y := H xp *ᵥ s + Δ *ᵥ s) hΔsym
        (by rw [add_sub_cancel_left])
      rw [psbUpdate_sub_eq_psbCorrection, add_sub_cancel_left] at this
      rw [this]
    rw [h1, psbUpdate_sub_eq_psbCorrection, h2, psbCorrection_sub, h3]
    abel
  -- the compression is bounded by `‖Δ‖`
  have hQt : Qᵀ = Q := by rw [hQ, transpose_sub, transpose_one, transpose_proj]
  have hQQ : Q * Q = Q := by
    rw [hQ, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul,
      Matrix.mul_one, proj_mul_proj hs]
    abel
  have hcomp : ‖Q * Δ * Q‖ ≤ ‖B - H x‖ + L * ‖toLp 2 s‖ := by
    have h1 : ‖Q * Δ * Q‖ ≤ ‖Δ‖ := by
      have h2 := frobenius_norm_sq_sub_mul_mul_add_sq Δ hQt hQQ
      exact le_of_sq_le_sq (by nlinarith [sq_nonneg ‖Δ - Q * Δ * Q‖]) (norm_nonneg _)
    have h2 : ‖Δ‖ ≤ ‖B - H x‖ + ‖H x - H xp‖ := by
      rw [hΔ, show B - H xp = (B - H x) + (H x - H xp) by abel]
      exact norm_add_le _ _
    have h3 : ‖H x - H xp‖ ≤ L * ‖toLp 2 s‖ := by
      have := hL _ hx _ hxs
      rwa [norm_sub_rev x xp, hsn] at this
    linarith
  -- the mean value estimate for the secant residual
  have hopL : ∀ z ∈ D, ‖toEuclideanCLM (𝕜 := ℝ) (H z) - toEuclideanCLM (𝕜 := ℝ) (H xp)‖
      ≤ L * ‖z - xp‖ := fun z hz => by
    rw [← map_sub]
    exact (norm_toEuclideanCLM_le_frobenius_norm _).trans (hL z hz xp hxs)
  have hmv : ‖toLp 2 w‖ ≤ L / 2 * ‖toLp 2 s‖ ^ 2 := by
    have h := Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le hD hg hxs hx hopL
    rw [show x - xp = -toLp 2 s from sub_add_cancel_left x (toLp 2 s), map_neg, norm_neg,
      toEuclideanCLM_toLp, sub_neg_eq_add] at h
    have heq : toLp 2 w = -(g x - g xp + toLp 2 (H xp *ᵥ s)) := by
      rw [hw, toLp_sub, toLp_ofLp]
      abel
    rw [heq, norm_neg]
    exact h
  have hcorr : ‖psbCorrection s w‖ ≤ 3 / 2 * L * ‖toLp 2 s‖ := by
    calc ‖psbCorrection s w‖ ≤ 3 * ‖toLp 2 w‖ / ‖toLp 2 s‖ := frobenius_norm_psbCorrection_le hs w
      _ ≤ 3 * (L / 2 * ‖toLp 2 s‖ ^ 2) / ‖toLp 2 s‖ := by gcongr
      _ = 3 / 2 * L * ‖toLp 2 s‖ := by field_simp
  calc ‖psbUpdate B s y - H xp‖ = ‖Q * Δ * Q + psbCorrection s w‖ := by rw [hdecomp]
    _ ≤ ‖Q * Δ * Q‖ + ‖psbCorrection s w‖ := norm_add_le _ _
    _ ≤ (‖B - H x‖ + L * ‖toLp 2 s‖) + 3 / 2 * L * ‖toLp 2 s‖ := add_le_add hcomp hcorr
    _ ≤ ‖B - H x‖ + 3 * L * ‖toLp 2 s‖ := by nlinarith [mul_nonneg hL0 hs0.le]

end Frobenius

/-! ### The BFGS and DFP updates -/

/-- For a symmetric matrix $B$, the bilinear form is symmetric: $u^T B v = v^T B u$. -/
theorem dotProduct_mulVec_comm_of_isSymm {B : Matrix n n ℝ} (hB : B.IsSymm) (u v : n → ℝ) :
    u ⬝ᵥ (B *ᵥ v) = v ⬝ᵥ (B *ᵥ u) :=
  hB.dotProduct_mulVec_comm

/-- **The Broyden–Fletcher–Goldfarb–Shanno update** of a Hessian approximation, (6.19) of
[nocedal2006numerical]:
$$B_+ = B - \frac{(Bs)(Bs)^T}{s^T B s} + \frac{y y^T}{y^T s}.$$
It satisfies the secant equation, preserves symmetry, and preserves positive definiteness under
the curvature condition $y^T s > 0$. Its inverse is the DFP update of the inverse, with the
roles of $s$ and $y$ exchanged.

The divisions give $0$ when a denominator vanishes. -/
noncomputable def bfgsUpdate (B : Matrix n n ℝ) (s y : n → ℝ) : Matrix n n ℝ :=
  B - (1 / (s ⬝ᵥ (B *ᵥ s))) • vecMulVec (B *ᵥ s) (B *ᵥ s) + (1 / (y ⬝ᵥ s)) • vecMulVec y y

/-- **The secant equation** for the BFGS update: if $s^T B s \neq 0$ and $y^T s \neq 0$, then
$B_+ s = y$. -/
theorem bfgsUpdate_mulVec (B : Matrix n n ℝ) {s y : n → ℝ} (hBs : s ⬝ᵥ (B *ᵥ s) ≠ 0)
    (hys : y ⬝ᵥ s ≠ 0) : bfgsUpdate B s y *ᵥ s = y := by
  rw [bfgsUpdate, add_mulVec, sub_mulVec, smul_mulVec, smul_mulVec, vecMulVec_mulVec,
    vecMulVec_mulVec, op_smul_eq_smul, op_smul_eq_smul, smul_smul,
    smul_smul, dotProduct_comm (B *ᵥ s) s, one_div_mul_cancel hBs, one_div_mul_cancel hys,
    one_smul, one_smul, sub_self, zero_add]

/-- If $B$ is symmetric, then the BFGS update is symmetric. -/
theorem bfgsUpdate_isSymm {B : Matrix n n ℝ} (hB : B.IsSymm) (s y : n → ℝ) :
    (bfgsUpdate B s y).IsSymm := by
  unfold IsSymm bfgsUpdate
  simp only [transpose_add, transpose_sub, transpose_smul, transpose_vecMulVec, hB.eq]

/-- **The BFGS update preserves positive definiteness under the curvature condition**; this is
Theorem 9.2.1 of [dennis1996numerical] in its BFGS form, see also Section 6.1 of
[nocedal2006numerical]. If $B$ is positive definite and $y^T s > 0$, then the BFGS update $B_+$
is positive definite.

For $z \neq 0$, let $t = (z^T B s) / (s^T B s)$ and $u = z - t s$. Then
$z^T B_+ z = u^T B u + (y^T z)^2 / (y^T s)$. The first term is positive unless $z = t s$; in
that case $t \neq 0$ and the second term is $t^2 y^T s > 0$. -/
theorem bfgsUpdate_posDef {B : Matrix n n ℝ} (hB : B.PosDef) {s y : n → ℝ} (hys : 0 < y ⬝ᵥ s) :
    (bfgsUpdate B s y).PosDef := by
  have hBs : B.IsSymm := isHermitian_iff_isSymm.1 hB.isHermitian
  have hs : s ≠ 0 := by
    rintro rfl
    simp at hys
  have ha : 0 < s ⬝ᵥ (B *ᵥ s) := by simpa using hB.dotProduct_mulVec_pos hs
  refine PosDef.of_dotProduct_mulVec_pos (isHermitian_iff_isSymm.2 (bfgsUpdate_isSymm hBs s y))
    fun z hz => ?_
  rw [star_trivial]
  set a : ℝ := s ⬝ᵥ (B *ᵥ s) with ha_def
  set b : ℝ := y ⬝ᵥ s with hb_def
  set t : ℝ := z ⬝ᵥ (B *ᵥ s) / a with ht_def
  have hq : z ⬝ᵥ (bfgsUpdate B s y *ᵥ z)
      = (z - t • s) ⬝ᵥ (B *ᵥ (z - t • s)) + 1 / b * (y ⬝ᵥ z) ^ 2 := by
    simp only [bfgsUpdate, sub_mulVec, add_mulVec, smul_mulVec, vecMulVec_mulVec,
      op_smul_eq_smul, dotProduct_sub, dotProduct_add, dotProduct_smul, mulVec_sub,
      mulVec_smul, sub_dotProduct, smul_dotProduct, smul_eq_mul, ← ha_def, ← hb_def]
    rw [dotProduct_comm (B *ᵥ s) z, dotProduct_mulVec_comm_of_isSymm hBs s z,
      dotProduct_comm z y, ht_def]
    field_simp
    ring
  rw [hq]
  by_cases hu : z - t • s = 0
  · have hz' : z = t • s := sub_eq_zero.1 hu
    have ht : t ≠ 0 := by
      rintro ht0
      rw [ht0, zero_smul] at hz'
      exact hz hz'
    rw [hu, mulVec_zero, dotProduct_zero, zero_add, hz', dotProduct_smul, smul_eq_mul, ← hb_def,
      show 1 / b * (t * b) ^ 2 = t ^ 2 * b by field_simp]
    positivity
  · have h := hB.dotProduct_mulVec_pos hu
    rw [star_trivial] at h
    have : 0 ≤ 1 / b * (y ⬝ᵥ z) ^ 2 := by positivity
    linarith

section DFP

variable [DecidableEq n]

/-- **The Davidon–Fletcher–Powell update** of a Hessian approximation, (9.2.7) of
[dennis1996numerical] and (6.13) of [nocedal2006numerical]. With $\rho = 1 / (y^T s)$,
$$B_+ = (I - \rho y s^T) B (I - \rho s y^T) + \rho y y^T.$$
It satisfies the secant equation, preserves symmetry, and preserves positive definiteness under
the curvature condition $y^T s > 0$.

This update is not in the text of [quarteroni2000numerical], which defers positive definite
updates to Section 9.2 of [dennis1996numerical]. If $y^T s = 0$, then $\rho = 0$ and $B_+ = B$. -/
noncomputable def dfpUpdate (B : Matrix n n ℝ) (s y : n → ℝ) : Matrix n n ℝ :=
  (1 - (1 / (y ⬝ᵥ s)) • vecMulVec y s) * B * (1 - (1 / (y ⬝ᵥ s)) • vecMulVec s y)
    + (1 / (y ⬝ᵥ s)) • vecMulVec y y

/-- **The secant equation** for the DFP update: if $y^T s \neq 0$, then $B_+ s = y$. -/
theorem dfpUpdate_mulVec (B : Matrix n n ℝ) {s y : n → ℝ} (hys : y ⬝ᵥ s ≠ 0) :
    dfpUpdate B s y *ᵥ s = y := by
  have h : (1 - (1 / (y ⬝ᵥ s)) • vecMulVec s y) *ᵥ s = 0 := by
    rw [sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul,
      smul_smul, one_div_mul_cancel hys, one_smul, sub_self]
  rw [dfpUpdate, add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, h, mulVec_zero, mulVec_zero,
    zero_add, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, smul_smul,
    one_div_mul_cancel hys, one_smul]

/-- If $B$ is symmetric, then the DFP update is symmetric. -/
theorem dfpUpdate_isSymm {B : Matrix n n ℝ} (hB : B.IsSymm) (s y : n → ℝ) :
    (dfpUpdate B s y).IsSymm := by
  unfold IsSymm dfpUpdate
  simp only [transpose_add, transpose_mul, transpose_sub, transpose_one, transpose_smul,
    transpose_vecMulVec, hB.eq, Matrix.mul_assoc]

/-- **The DFP update preserves positive definiteness under the curvature condition**, Theorem 9.2.1
of [dennis1996numerical]; see also Section 6.1 of [nocedal2006numerical]. If $B$ is positive
definite and $y^T s > 0$, then the DFP update $B_+$ is positive definite.

For $z \neq 0$, let $w = (I - \rho s y^T) z = z - \rho (y^T z) s$. Then
$z^T B_+ z = w^T B w + \rho (y^T z)^2$. The first term is positive unless $w = 0$; in that case
$y^T z \neq 0$, since otherwise $z = 0$, and the second term is positive. -/
theorem dfpUpdate_posDef {B : Matrix n n ℝ} (hB : B.PosDef) {s y : n → ℝ} (hys : 0 < y ⬝ᵥ s) :
    (dfpUpdate B s y).PosDef := by
  have hBs : B.IsSymm := isHermitian_iff_isSymm.1 hB.isHermitian
  refine PosDef.of_dotProduct_mulVec_pos (isHermitian_iff_isSymm.2 (dfpUpdate_isSymm hBs s y))
    fun z hz => ?_
  rw [star_trivial]
  set ρ : ℝ := 1 / (y ⬝ᵥ s) with hρ
  set N : Matrix n n ℝ := 1 - ρ • vecMulVec s y with hN
  have hNt : (1 - ρ • vecMulVec y s)ᵀ = N := by
    rw [transpose_sub, transpose_one, transpose_smul, transpose_vecMulVec]
  have hNz : N *ᵥ z = z - (ρ * (y ⬝ᵥ z)) • s := by
    rw [hN, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec,
      op_smul_eq_smul, smul_smul]
  have hq : z ⬝ᵥ (dfpUpdate B s y *ᵥ z) = (N *ᵥ z) ⬝ᵥ (B *ᵥ (N *ᵥ z)) + ρ * (y ⬝ᵥ z) ^ 2 := by
    rw [dfpUpdate, ← hρ, ← hN, add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_add,
      dotProduct_mulVec, ← mulVec_transpose, hNt, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul,
      dotProduct_smul, dotProduct_smul, dotProduct_comm z y, smul_eq_mul, smul_eq_mul, sq]
  rw [hq]
  by_cases hw : N *ᵥ z = 0
  · have hyz : y ⬝ᵥ z ≠ 0 := by
      intro h0
      rw [hNz, h0, mul_zero, zero_smul, sub_zero] at hw
      exact hz hw
    rw [hw, mulVec_zero, dotProduct_zero, zero_add]
    positivity
  · have h := hB.dotProduct_mulVec_pos hw
    rw [star_trivial] at h
    have : 0 ≤ ρ * (y ⬝ᵥ z) ^ 2 := by positivity
    linarith

end DFP

end Matrix
