/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Matrix.Function.CFC
import Numlib.Analysis.Matrix.Function.Sign
import Numlib.Analysis.Matrix.SingularValues
import Numlib.LinearAlgebra.Matrix.OrthogonalTrace
import Numlib.LinearAlgebra.Matrix.Polar
import Numlib.LinearAlgebra.Matrix.PosDef

/-!
# The polar decomposition as a function of matrices

A polar decomposition of $A \in \mathbb{K}^{m \times n}$ is a factorization $A = UP$ in which $U$
has orthonormal columns and $P$ is positive semidefinite. The definition
`Matrix.IsPolarDecomposition`, the existence of the factorization and the formula
$P = (A^H A)^{1/2}$ are in `Numlib.LinearAlgebra.Matrix.Polar`. This module proves the facts about
the polar decomposition that belong to the functions of matrices in [golub2013matrix], §9.4.3: $P$
is the primary square root of $A^H A$; for a nonsingular square $A$, Newton's iteration $X_0 = A$,
$X_{k+1} = (X_k + X_k^{-H})/2$ converges quadratically to $U$; the unitary factor satisfies the
perturbation bounds of Li and Sun; and the sign of the matrix
$\begin{bmatrix} 0 & A \\ A^H & 0 \end{bmatrix}$ is
$\begin{bmatrix} 0 & U \\ U^H & 0 \end{bmatrix}$.

The perturbation bounds are from W. Li and W. Sun, *Perturbation bounds of unitary and subunitary
polar factors*, SIAM J. Matrix Anal. Appl. 23 (2002) 1183–1193, which [golub2013matrix] quotes. For
square $A$ and $\tilde A$ with polar decompositions $A = UP$ and $\tilde A = \tilde U P'$, the
complex bound is $\|U - \tilde U\|_F \le 2 \|A - \tilde A\|_F / (\sigma_{\min}(A) +
\sigma_{\min}(\tilde A))$. The real bound, under the condition $\det A \cdot \det \tilde A > 0$, has
the numerator $4 \|A - \tilde A\|_F$ and the sum of the two smallest singular values of $A$ and of
$\tilde A$ as the denominator.

## Main definitions

* `Matrix.newtonPolarIterate`: Newton's polar iteration $X_0 = A$, $X_{k+1} = (X_k + X_k^{-H})/2$.

## Main results

* `Matrix.IsPolarDecomposition.eq_pfc_sqrt`: $P$ is the primary square root of $A^H A$.
* `Matrix.newtonPolarIterate_eq`: for nonsingular $A = UP$, $X_k = U P_k$, where $P_k$ is Newton's
  polar iteration started at $P$.
* `Matrix.l2_opNorm_newtonPolarIterate_sub`: $\|X_k - U\|_2 = \|P_k - I\|_2$.
* `Matrix.newtonPolarIterate_succ_sub_one`: $P_{k+1} - I = \frac12 P_k^{-1} (P_k - I)^2$ for
  positive definite $P$.
* `Matrix.tendsto_newtonPolarIterate`: $X_k \to U$ for nonsingular $A = UP$.
* `Matrix.frobenius_norm_le_of_mul_add_mul_eq`: if $P \succeq \sigma I$, $Q \succeq \tau I$,
  $\sigma + \tau > 0$ and $PX + XQ = R$, then $\|X\|_F \le \|R\|_F / (\sigma + \tau)$.
* `Matrix.IsPolarDecomposition.frobenius_norm_sub_le_div_iInf_colSingularValues`: the complex Li–Sun
  bound.
* `Matrix.frobenius_norm_polar_sub_le`: the real Li–Sun bound.
* `Matrix.matrixSign_hermitianDilation`: for nonsingular $A = UP$, the sign of
  $\begin{bmatrix} 0 & A \\ A^H & 0 \end{bmatrix}$ is
  $\begin{bmatrix} 0 & U \\ U^H & 0 \end{bmatrix}$.

## Proof outline

The convergence proof diagonalizes $P = V \operatorname{diag}(\sigma) V^H$ with
`Matrix.IsHermitian.spectral_theorem`. Then $P_k = V \operatorname{diag}(r_k(\sigma_i)) V^H$, where
$r_k$ are the iterates of the scalar Newton map $r \mapsto (r + 1/r)/2$, and these converge to $1$
from every $r > 0$. So the proof needs no complex sign function.

The real Li–Sun bound is not proved as Li and Sun prove it. Let $W = U^T \tilde U$, which is a
rotation because $\det A \cdot \det \tilde A > 0$, and let $X = I - W$. Then $PX + XP' = R$ with
$\|R\|_F \le 2 \|A - \tilde A\|_F$, and the identity $X X^T = X^T X = X + X^T$ turns
$\operatorname{tr}(X^T R)$ into $2 \operatorname{tr}(PX) + 2 \operatorname{tr}(P'X)$. The pairing
inequality `Matrix.le_trace_mul_one_sub` bounds each trace from below. This inequality needs only
two facts about orthogonal matrices $O$: $\operatorname{tr}(RO) \le \operatorname{tr} R$ for
$R \succeq 0$ (`Matrix.PosSemidef.trace_mul_le_trace`), and $\operatorname{tr} O \le n - 2$ when
$\det O = -1$ (`Matrix.trace_le_card_sub_two_of_det_eq_neg_one`), applied to $O = (I - 2uu^T) W$.

## Implementation notes

* Every statement about the polar factor $U$ takes a hypothesis `Matrix.IsPolarDecomposition A U P`.
* The field $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$ (`RCLike`). The real Li–Sun bound is over
  $\mathbb{R}$, and the sign of the block matrix is over $\mathbb{C}$.
* $\|\cdot\|_2$ is the spectral norm of `Matrix.Norms.L2Operator`, and $\|\cdot\|_F$ is the
  Frobenius norm of `Matrix.Norms.Frobenius`.
* A lower bound $P \succeq \sigma I$ in the Loewner order is written `(P - (σ : 𝕜) • 1).PosSemidef`.
* The block matrix $\begin{bmatrix} 0 & A \\ A^H & 0 \end{bmatrix}$ is
  `Matrix.hermitianDilation Aᴴ`.
-/

open Filter Topology
open scoped ComplexOrder

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜]

section Sqrt

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

open scoped MatrixOrder in
/-- Let $A \in \mathbb{K}^{m \times n}$ have the polar decomposition $A = UP$. Then **$P$ is the
primary square root of $A^H A$**:
$$P = f(A^H A), \qquad f(z) = \sqrt{\operatorname{Re} z},$$
where $f(A^H A)$ is the primary functional calculus `pfc`. This is the formula
$P = (A^T A)^{1/2}$ of [golub2013matrix], §9.4.3, read in the functional calculus of Chapter 9
of [golub2013matrix].

The function $f$ agrees with the square root on $[0, \infty)$, which contains the eigenvalues of
$A^H A$. The proof combines `Matrix.IsPolarDecomposition.eq_cfcSqrt` and
`Matrix.PosSemidef.cfcSqrt_eq_pfc`. -/
theorem IsPolarDecomposition.eq_pfc_sqrt {A U : Matrix m n 𝕜} {P : Matrix n n 𝕜}
    (h : IsPolarDecomposition A U P) :
    P = pfc (fun z : 𝕜 => ((Real.sqrt (RCLike.re z) : ℝ) : 𝕜)) (Aᴴ * A) := by
  rw [h.eq_cfcSqrt, (posSemidef_conjTranspose_mul_self A).cfcSqrt_eq_pfc]

end Sqrt

section Newton

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Newton's polar iteration**: for a square matrix $A$,
$$X_0 = A, \qquad X_{k+1} = \tfrac12 \big(X_k + X_k^{-H}\big),$$
where $X^{-H} = (X^{-1})^H$. This is (9.4.11) of [golub2013matrix].

The formula is the one that (9.4.12) of [golub2013matrix] implies. The inverse is the Mathlib
matrix inverse, which is $0$ at a singular matrix. -/
noncomputable def newtonPolarIterate (A : Matrix n n 𝕜) : ℕ → Matrix n n 𝕜
  | 0 => A
  | k + 1 => (2 : 𝕜)⁻¹ • (newtonPolarIterate A k + (newtonPolarIterate A k)⁻¹ᴴ)

/-- Newton's polar iteration starts at $X_0 = A$. -/
@[simp]
theorem newtonPolarIterate_zero (A : Matrix n n 𝕜) : newtonPolarIterate A 0 = A := rfl

/-- Newton's polar iteration satisfies $X_{k+1} = (X_k + X_k^{-H})/2$. -/
theorem newtonPolarIterate_succ (A : Matrix n n 𝕜) (k : ℕ) :
    newtonPolarIterate A (k + 1)
      = (2 : 𝕜)⁻¹ • (newtonPolarIterate A k + (newtonPolarIterate A k)⁻¹ᴴ) := rfl

/-- The scalar Newton map $r \mapsto (r + 1/r)/2$, iterated from $s$. -/
private noncomputable def newtonScalar (s : ℝ) : ℕ → ℝ
  | 0 => s
  | k + 1 => 2⁻¹ * (newtonScalar s k + (newtonScalar s k)⁻¹)

private theorem newtonScalar_pos {s : ℝ} (hs : 0 < s) (k : ℕ) : 0 < newtonScalar s k := by
  induction k with
  | zero => exact hs
  | succ k ih =>
    change 0 < 2⁻¹ * (newtonScalar s k + (newtonScalar s k)⁻¹)
    positivity

/-- From the first step on, the scalar Newton iterates $r_k$ from $s > 0$ satisfy $r_{k+1} \ge 1$
and $r_{k+1} - 1 \le (r_1 - 1)/2^k$, because $(r + 1/r)/2 - 1 = (r - 1)^2/(2r) \le (r - 1)/2$
for $r \ge 1$. -/
private theorem newtonScalar_succ_bounds {s : ℝ} (hs : 0 < s) (k : ℕ) :
    1 ≤ newtonScalar s (k + 1) ∧
      newtonScalar s (k + 1) - 1 ≤ (newtonScalar s 1 - 1) / 2 ^ k := by
  induction k with
  | zero =>
    refine ⟨?_, by simp⟩
    change 1 ≤ 2⁻¹ * (s + s⁻¹)
    have : 2 ≤ s + s⁻¹ := by
      have h1 : s + s⁻¹ - 2 = (s - 1) ^ 2 / s := by field_simp; ring
      nlinarith [div_nonneg (sq_nonneg (s - 1)) hs.le]
    linarith
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    set r := newtonScalar s (k + 1) with hr
    have heq : newtonScalar s (k + 1 + 1) - 1 = (r - 1) ^ 2 / (2 * r) := by
      change 2⁻¹ * (r + r⁻¹) - 1 = _
      field_simp
      ring
    have hle : (r - 1) ^ 2 / (2 * r) ≤ (r - 1) / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    refine ⟨by nlinarith [div_nonneg (sq_nonneg (r - 1)) (by positivity : (0 : ℝ) ≤ 2 * r)], ?_⟩
    calc newtonScalar s (k + 1 + 1) - 1 = (r - 1) ^ 2 / (2 * r) := heq
      _ ≤ (r - 1) / 2 := hle
      _ ≤ (newtonScalar s 1 - 1) / 2 ^ k / 2 := div_le_div_of_nonneg_right h2 (by norm_num)
      _ = (newtonScalar s 1 - 1) / 2 ^ (k + 1) := by rw [pow_succ, div_div]

/-- The scalar Newton iterates converge to $1$ from every $s > 0$. -/
private theorem tendsto_newtonScalar {s : ℝ} (hs : 0 < s) :
    Tendsto (newtonScalar s) atTop (𝓝 1) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  have hup : Tendsto (fun k : ℕ => 1 + (newtonScalar s 1 - 1) / 2 ^ k) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := newtonScalar s 1 - 1)).div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
    simpa using this.const_add 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun k => ?_)
    fun k => ?_
  · exact (newtonScalar_succ_bounds hs k).1
  · have := (newtonScalar_succ_bounds hs k).2
    simp only
    linarith

/-- For unitary $V$ and a real diagonal matrix $D$ with nonzero diagonal entries,
$(V D V^H)^{-1} = V D^{-1} V^H$. -/
private theorem inv_conj_diagonal {V : Matrix n n 𝕜} (hV : V ∈ unitaryGroup n 𝕜) {d : n → ℝ}
    (hd : ∀ i, d i ≠ 0) :
    (V * diagonal (fun i => ((d i : ℝ) : 𝕜)) * Vᴴ)⁻¹
      = V * diagonal (fun i => (((d i)⁻¹ : ℝ) : 𝕜)) * Vᴴ := by
  have hVV : Vᴴ * V = 1 := conjTranspose_mul_self_of_mem_unitaryGroup hV
  refine inv_eq_left_inv ?_
  calc V * diagonal (fun i => (((d i)⁻¹ : ℝ) : 𝕜)) * Vᴴ *
        (V * diagonal (fun i => ((d i : ℝ) : 𝕜)) * Vᴴ)
      = V * (diagonal (fun i => (((d i)⁻¹ : ℝ) : 𝕜)) * (Vᴴ * V) *
          diagonal (fun i => ((d i : ℝ) : 𝕜))) * Vᴴ := by simp only [Matrix.mul_assoc]
    _ = V * Vᴴ := by
        rw [hVV, Matrix.mul_one, diagonal_mul_diagonal,
          show (fun i => (((d i)⁻¹ : ℝ) : 𝕜) * ((d i : ℝ) : 𝕜)) = fun _ => 1 from
            funext fun i => by rw [← RCLike.ofReal_mul, inv_mul_cancel₀ (hd i),
              RCLike.ofReal_one], diagonal_one, Matrix.mul_one]
    _ = 1 := mul_conjTranspose_self_of_mem_unitaryGroup hV

/-- If $P = V \operatorname{diag}(s) V^H$ with $V$ unitary and $s > 0$, then the Newton polar
iterates of $P$ are $P_k = V \operatorname{diag}(r_k(s_i)) V^H$, with the scalar Newton iterates
$r_k$. -/
private theorem newtonPolarIterate_conj_diagonal {V : Matrix n n 𝕜} (hV : V ∈ unitaryGroup n 𝕜)
    {s : n → ℝ} (hs : ∀ i, 0 < s i) (k : ℕ) :
    newtonPolarIterate (V * diagonal (fun i => ((s i : ℝ) : 𝕜)) * Vᴴ) k
      = V * diagonal (fun i => ((newtonScalar (s i) k : ℝ) : 𝕜)) * Vᴴ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hH : (V * diagonal (fun i => (((newtonScalar (s i) k)⁻¹ : ℝ) : 𝕜)) * Vᴴ)ᴴ
        = V * diagonal (fun i => (((newtonScalar (s i) k)⁻¹ : ℝ) : 𝕜)) * Vᴴ := by
      have hstar : star (fun i => (((newtonScalar (s i) k)⁻¹ : ℝ) : 𝕜))
          = fun i => (((newtonScalar (s i) k)⁻¹ : ℝ) : 𝕜) := funext fun i => by simp
      rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
        diagonal_conjTranspose, hstar, Matrix.mul_assoc]
    rw [newtonPolarIterate_succ, ih,
      inv_conj_diagonal hV fun i => (newtonScalar_pos (hs i) k).ne', hH, ← Matrix.add_mul,
      ← Matrix.mul_add, diagonal_add, ← Matrix.smul_mul, ← Matrix.mul_smul, ← diagonal_smul]
    congr 3
    funext i
    rw [Pi.smul_apply, smul_eq_mul]
    change _ = ((2⁻¹ * (newtonScalar (s i) k + (newtonScalar (s i) k)⁻¹) : ℝ) : 𝕜)
    push_cast
    ring

/-- Let $P \in \mathbb{K}^{n \times n}$ be positive definite. Then every iterate $P_k$ of Newton's
polar iteration started at $P$ is positive definite. -/
theorem PosDef.newtonPolarIterate {P : Matrix n n 𝕜} (hP : P.PosDef) (k : ℕ) :
    (newtonPolarIterate P k).PosDef := by
  have hV := hP.isHermitian.eigenvectorUnitary.2
  rw [hP.isHermitian.eq_conj_diagonal, newtonPolarIterate_conj_diagonal hV hP.eigenvalues_pos]
  have hD : (diagonal fun i => ((newtonScalar (hP.isHermitian.eigenvalues i) k : ℝ) : 𝕜)).PosDef :=
    posDef_diagonal_iff.2 fun i => RCLike.ofReal_pos.2 (newtonScalar_pos (hP.eigenvalues_pos i) k)
  have hinj : Function.Injective
      ((hP.isHermitian.eigenvectorUnitary : Matrix n n 𝕜)ᴴ).mulVec := by
    refine mulVec_injective_iff_isUnit.2 ?_
    rw [← star_eq_conjTranspose]
    exact isUnit_of_mem_unitaryGroup (Unitary.star_mem hV)
  simpa using hD.conjTranspose_mul_mul_same hinj

variable {A U P : Matrix n n 𝕜}

/-- **Newton's polar iterates in polar form.** Let $A \in \mathbb{K}^{n \times n}$ be nonsingular
with polar decomposition $A = UP$, and let $X_k$ and $P_k$ be the iterates of Newton's polar
iteration started at $A$ and at $P$. Then for every $k$,
$$X_k = U P_k,$$
and $P_k$ is positive definite. This is (9.4.12) of [golub2013matrix].

Since every $P_k$ is Hermitian, $P_{k+1} = (P_k + P_k^{-1})/2$ is the Newton sign iteration of
$P$. Since every $P_k$ is positive definite, every $X_k$ is nonsingular. The proof is an
induction that uses $(U P_k)^{-H} = U P_k^{-H}$ for unitary $U$. -/
theorem newtonPolarIterate_eq (hA : IsUnit A) (h : IsPolarDecomposition A U P) (k : ℕ) :
    newtonPolarIterate A k = U * newtonPolarIterate P k ∧ (newtonPolarIterate P k).PosDef := by
  have hP : P.PosDef := h.posSemidef.posDef_iff_isUnit.2 (h.isUnit hA)
  have hUi : U⁻¹ = Uᴴ := inv_eq_left_inv h.conjTranspose_mul_self
  refine ⟨?_, hP.newtonPolarIterate k⟩
  induction k with
  | zero => exact h.eq_mul
  | succ k ih =>
    rw [newtonPolarIterate_succ, newtonPolarIterate_succ, ih, mul_inv_rev, hUi, conjTranspose_mul,
      conjTranspose_conjTranspose, ← Matrix.mul_add, Matrix.mul_smul]

open scoped Matrix.Norms.L2Operator in
/-- **The error of Newton's polar iteration.** Let $A \in \mathbb{K}^{n \times n}$ be nonsingular
with polar decomposition $A = UP$, and let $X_k$ and $P_k$ be the iterates of Newton's polar
iteration started at $A$ and at $P$. Then for every $k$, in the spectral norm,
$$\|X_k - U\|_2 = \|P_k - I\|_2.$$
This is in [golub2013matrix], §9.4.3.

The proof writes $X_k - U = U (P_k - I)$ and uses that $U$ is unitary. -/
theorem l2_opNorm_newtonPolarIterate_sub (hA : IsUnit A) (h : IsPolarDecomposition A U P)
    (k : ℕ) :
    ‖newtonPolarIterate A k - U‖ = ‖newtonPolarIterate P k - 1‖ := by
  rw [(newtonPolarIterate_eq hA h k).1, ← Matrix.mul_one U, Matrix.mul_assoc, ← Matrix.mul_sub,
    Matrix.one_mul]
  exact l2_opNorm_mul_of_conjTranspose_mul_self_eq_one h.conjTranspose_mul_self _

/-- **The quadratic step of Newton's polar iteration.** Let $P \in \mathbb{K}^{n \times n}$ be
positive definite, and let $P_k$ be the iterates of Newton's polar iteration started at $P$.
Then for every $k$,
$$P_{k+1} - I = \tfrac12 P_k^{-1} (P_k - I)^2.$$
-/
theorem newtonPolarIterate_succ_sub_one {P : Matrix n n 𝕜} (hP : P.PosDef) (k : ℕ) :
    newtonPolarIterate P (k + 1) - 1
      = (2 : 𝕜)⁻¹ • ((newtonPolarIterate P k)⁻¹ *
          ((newtonPolarIterate P k - 1) * (newtonPolarIterate P k - 1))) := by
  have hk := hP.newtonPolarIterate k
  have hdet : IsUnit (newtonPolarIterate P k).det :=
    (isUnit_iff_isUnit_det _).1 hk.isUnit
  rw [newtonPolarIterate_succ, hk.inv.isHermitian.eq]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, ← Matrix.mul_assoc,
    nonsing_inv_mul _ hdet]
  module

open scoped Matrix.Norms.L2Operator in
/-- **Quadratic convergence of Newton's polar iteration.** Let $P \in \mathbb{K}^{n \times n}$ be
positive definite, and let $P_k$ be the iterates of Newton's polar iteration started at $P$.
Then for every $k$, in the spectral norm,
$$\|P_{k+1} - I\|_2 \le \tfrac12 \|P_k^{-1}\|_2\, \|P_k - I\|_2^2.$$
This is the step bound of [golub2013matrix], §9.4.3. -/
theorem l2_opNorm_newtonPolarIterate_succ_sub_one_le {P : Matrix n n 𝕜} (hP : P.PosDef)
    (k : ℕ) :
    ‖newtonPolarIterate P (k + 1) - 1‖
      ≤ ‖(newtonPolarIterate P k)⁻¹‖ * ‖newtonPolarIterate P k - 1‖ ^ 2 / 2 := by
  rw [newtonPolarIterate_succ_sub_one hP k, norm_smul, norm_inv, RCLike.norm_ofNat]
  have h1 := l2_opNorm_mul (newtonPolarIterate P k)⁻¹
    ((newtonPolarIterate P k - 1) * (newtonPolarIterate P k - 1))
  have h2 := l2_opNorm_mul (newtonPolarIterate P k - 1) (newtonPolarIterate P k - 1)
  have h3 : ‖(newtonPolarIterate P k)⁻¹‖ * ‖(newtonPolarIterate P k - 1) *
      (newtonPolarIterate P k - 1)‖ ≤ ‖(newtonPolarIterate P k)⁻¹‖ *
        (‖newtonPolarIterate P k - 1‖ * ‖newtonPolarIterate P k - 1‖) :=
    mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
  rw [sq]
  linarith

/-- **Newton's polar iteration converges to the unitary polar factor.** Let
$A \in \mathbb{K}^{n \times n}$ be nonsingular with polar decomposition $A = UP$, and let $X_k$
be the iterates of Newton's polar iteration started at $A$. Then $X_k \to U$ as $k \to \infty$.
This is in [golub2013matrix], §9.4.3. The convergence is quadratic by
`Matrix.l2_opNorm_newtonPolarIterate_succ_sub_one_le`.

In an eigenbasis $P = V \operatorname{diag}(\sigma) V^H$, the iterates are $X_k = U V
\operatorname{diag}(r_k(\sigma_i)) V^H$, where $r_k$ are the iterates of the scalar Newton map
$r \mapsto (r + 1/r)/2$, and $r_k(\sigma) \to 1$. -/
theorem tendsto_newtonPolarIterate (hA : IsUnit A) (h : IsPolarDecomposition A U P) :
    Tendsto (newtonPolarIterate A) atTop (𝓝 U) := by
  have hP : P.PosDef := h.posSemidef.posDef_iff_isUnit.2 (h.isUnit hA)
  set V := (hP.isHermitian.eigenvectorUnitary : Matrix n n 𝕜) with hVdef
  have hV : V ∈ unitaryGroup n 𝕜 := hP.isHermitian.eigenvectorUnitary.2
  set s := hP.isHermitian.eigenvalues with hsdef
  have hs : ∀ i, 0 < s i := hP.eigenvalues_pos
  have hform : ∀ k, newtonPolarIterate A k
      = U * (V * diagonal (fun i => ((newtonScalar (s i) k : ℝ) : 𝕜)) * Vᴴ) := fun k => by
    rw [(newtonPolarIterate_eq hA h k).1, hP.isHermitian.eq_conj_diagonal,
      newtonPolarIterate_conj_diagonal hV hs]
  have hlim : Tendsto (fun k => fun i => ((newtonScalar (s i) k : ℝ) : 𝕜)) atTop
      (𝓝 fun _ => (1 : 𝕜)) := by
    rw [tendsto_pi_nhds]
    intro i
    have := ((RCLike.continuous_ofReal (K := 𝕜)).tendsto 1).comp (tendsto_newtonScalar (hs i))
    simpa [Function.comp_def] using this
  have hc : Continuous fun d : n → 𝕜 => U * (V * diagonal d * Vᴴ) :=
    continuous_const.matrix_mul
      ((continuous_const.matrix_mul continuous_id.matrix_diagonal).matrix_mul continuous_const)
  have hval : U * (V * diagonal (fun _ => (1 : 𝕜)) * Vᴴ) = U := by
    rw [diagonal_one, Matrix.mul_one, ← star_eq_conjTranspose, mem_unitaryGroup_iff.1 hV,
      Matrix.mul_one]
  have := (hc.tendsto _).comp hlim
  rw [hval] at this
  exact this.congr fun k => (hform k).symm

end Newton

/-! ### Perturbation of the unitary polar factor -/

section Perturbation

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.Frobenius

/-- **A Sylvester equation with coefficients bounded below.** Let
$P, Q, X, R \in \mathbb{K}^{n \times n}$ and $\sigma, \tau \in \mathbb{R}$ with
$\sigma + \tau > 0$. Suppose that $P - \sigma I$ and $Q - \tau I$ are positive semidefinite, and
that $PX + XQ = R$. Then
$$\|X\|_F \le \frac{\|R\|_F}{\sigma + \tau}.$$
This is the step behind the perturbation bound of Li and Sun (2002) for the polar factor.

The proof is $(\sigma + \tau) \|X\|_F^2 \le \operatorname{Re} \operatorname{tr}(X^H P X) +
\operatorname{Re} \operatorname{tr}(X Q X^H) = \operatorname{Re} \operatorname{tr}(X^H R) \le
\|X\|_F \|R\|_F$. -/
theorem frobenius_norm_le_of_mul_add_mul_eq {P Q X R : Matrix n n 𝕜} {σ τ : ℝ}
    (hP : (P - (σ : 𝕜) • 1).PosSemidef) (hQ : (Q - (τ : 𝕜) • 1).PosSemidef)
    (hστ : 0 < σ + τ) (h : P * X + X * Q = R) : ‖X‖ ≤ ‖R‖ / (σ + τ) := by
  have hX2 := frobenius_norm_sq_eq_trace X
  have hXX : trace (X * Xᴴ) = trace (Xᴴ * X) := trace_mul_comm X Xᴴ
  have h1 : σ * ‖X‖ ^ 2 ≤ RCLike.re (trace (Xᴴ * P * X)) := by
    have h0 := RCLike.nonneg_iff.1 (hP.conjTranspose_mul_mul_same X).trace_nonneg
    rw [Matrix.mul_sub, Matrix.sub_mul, trace_sub, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, trace_smul, ← hX2, smul_eq_mul, map_sub, ← RCLike.ofReal_mul,
      RCLike.ofReal_re] at h0
    linarith [h0.1]
  have h2 : τ * ‖X‖ ^ 2 ≤ RCLike.re (trace (Xᴴ * X * Q)) := by
    have h0 := RCLike.nonneg_iff.1 (hQ.mul_mul_conjTranspose_same X).trace_nonneg
    rw [Matrix.mul_sub, Matrix.sub_mul, trace_sub, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, trace_smul, hXX, ← hX2, smul_eq_mul, map_sub, ← RCLike.ofReal_mul,
      RCLike.ofReal_re, trace_mul_comm (X * Q), ← Matrix.mul_assoc] at h0
    linarith [h0.1]
  have h3 : RCLike.re (trace (Xᴴ * R)) = RCLike.re (trace (Xᴴ * P * X))
      + RCLike.re (trace (Xᴴ * X * Q)) := by
    rw [← h, Matrix.mul_add, trace_add, map_add, Matrix.mul_assoc, Matrix.mul_assoc]
  have h4 := re_trace_conjTranspose_mul_le X R
  rw [le_div_iff₀ hστ]
  rcases (norm_nonneg X).eq_or_lt with hX | hX
  · rw [← hX, zero_mul]
    exact norm_nonneg R
  · refine le_of_mul_le_mul_right ?_ hX
    nlinarith

/-- For polar decompositions $A = UP$ and $\tilde A = \tilde U P'$ and $\Delta = A - \tilde A$, the
matrix $X = U^H (U - \tilde U)$ satisfies $\|X\|_F = \|U - \tilde U\|_F$ and
$PX + XP' = U^H \Delta - \Delta^H \tilde U$, and the right side has Frobenius norm at most
$2 \|\Delta\|_F$. -/
private theorem IsPolarDecomposition.sylvester {A Ã U Ũ P P' : Matrix n n 𝕜}
    (h : IsPolarDecomposition A U P) (h' : IsPolarDecomposition Ã Ũ P') :
    ‖Uᴴ * (U - Ũ)‖ = ‖U - Ũ‖ ∧
      P * (Uᴴ * (U - Ũ)) + Uᴴ * (U - Ũ) * P' = Uᴴ * (A - Ã) - (A - Ã)ᴴ * Ũ ∧
      ‖Uᴴ * (A - Ã) - (A - Ã)ᴴ * Ũ‖ ≤ 2 * ‖A - Ã‖ := by
  have hU' := h'.mem_unitaryGroup
  have hUs : Uᴴ ∈ unitaryGroup n 𝕜 := by
    rw [← star_eq_conjTranspose]; exact Unitary.star_mem h.mem_unitaryGroup
  have hUU : Uᴴ * U = 1 := h.conjTranspose_mul_self
  have hUU' : Ũᴴ * Ũ = 1 := h'.conjTranspose_mul_self
  have hPh : Pᴴ = P := h.isHermitian
  have hPh' : P'ᴴ = P' := h'.isHermitian
  refine ⟨?_, ?_, ?_⟩
  · have := frobenius_norm_unitary_mul_mul_unitary hUs (U - Ũ) (one_mem (unitaryGroup n 𝕜))
    rwa [Matrix.mul_one] at this
  · have e1 : Uᴴ * (A - Ã) = P - Uᴴ * Ũ * P' := by
      rw [Matrix.mul_sub, h.eq_mul, h'.eq_mul, ← Matrix.mul_assoc, hUU, Matrix.one_mul,
        Matrix.mul_assoc]
    have e2 : (A - Ã)ᴴ * Ũ = P * (Uᴴ * Ũ) - P' := by
      rw [conjTranspose_sub, Matrix.sub_mul, h.eq_mul, h'.eq_mul, conjTranspose_mul,
        conjTranspose_mul, hPh, hPh', Matrix.mul_assoc, Matrix.mul_assoc, hUU', Matrix.mul_one]
    rw [e1, e2]
    simp only [Matrix.mul_sub, Matrix.sub_mul, hUU, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_assoc]
    abel
  · have h1 : ‖Uᴴ * (A - Ã)‖ = ‖A - Ã‖ := by
      have := frobenius_norm_unitary_mul_mul_unitary hUs (A - Ã) (one_mem (unitaryGroup n 𝕜))
      rwa [Matrix.mul_one] at this
    have h2 : ‖(A - Ã)ᴴ * Ũ‖ = ‖A - Ã‖ := by
      have := frobenius_norm_unitary_mul_mul_unitary (one_mem (unitaryGroup n 𝕜)) (A - Ã)ᴴ hU'
      rw [Matrix.one_mul] at this
      rw [this, frobenius_norm_conjTranspose]
    calc ‖Uᴴ * (A - Ã) - (A - Ã)ᴴ * Ũ‖ ≤ ‖Uᴴ * (A - Ã)‖ + ‖(A - Ã)ᴴ * Ũ‖ := norm_sub_le _ _
      _ = 2 * ‖A - Ã‖ := by rw [h1, h2]; ring

/-- **The perturbation of the unitary polar factor.** Let $A, \tilde A \in \mathbb{K}^{n \times n}$
have polar decompositions $A = UP$ and $\tilde A = \tilde U P'$, and let
$\sigma, \sigma' \in \mathbb{R}$ with $\sigma + \sigma' > 0$ be such that $P - \sigma I$ and
$P' - \sigma' I$ are positive semidefinite. Then
$$\|U - \tilde U\|_F \le \frac{2 \|A - \tilde A\|_F}{\sigma + \sigma'}.$$
This is the complex form of the bound of Li and Sun (2002), quoted in [golub2013matrix], §9.4.3.
One can take for $\sigma$ and $\sigma'$ the smallest singular values of $A$ and $\tilde A$; see
`Matrix.IsPolarDecomposition.frobenius_norm_sub_le_div_iInf_colSingularValues`.

With $W = U^H \tilde U$ and $\Delta = A - \tilde A$, the matrix $X = I - W$ solves
$PX + XP' = U^H \Delta - \Delta^H \tilde U$, so `Matrix.frobenius_norm_le_of_mul_add_mul_eq`
applies, and $\|X\|_F = \|U - \tilde U\|_F$. The real refinement with the two smallest singular
values is `Matrix.IsPolarDecomposition.frobenius_norm_sub_le_of_det_mul_pos`. -/
theorem IsPolarDecomposition.frobenius_norm_sub_le {A Ã U Ũ P P' : Matrix n n 𝕜}
    (h : IsPolarDecomposition A U P) (h' : IsPolarDecomposition Ã Ũ P') {σ σ' : ℝ}
    (hP : (P - (σ : 𝕜) • 1).PosSemidef) (hP' : (P' - (σ' : 𝕜) • 1).PosSemidef)
    (hσ : 0 < σ + σ') : ‖U - Ũ‖ ≤ 2 * ‖A - Ã‖ / (σ + σ') := by
  obtain ⟨hX, hsyl, hR⟩ := h.sylvester h'
  rw [← hX]
  calc ‖Uᴴ * (U - Ũ)‖ ≤ ‖Uᴴ * (A - Ã) - (A - Ã)ᴴ * Ũ‖ / (σ + σ') :=
        frobenius_norm_le_of_mul_add_mul_eq hP hP' hσ hsyl
    _ ≤ 2 * ‖A - Ã‖ / (σ + σ') := div_le_div_of_nonneg_right hR hσ.le

/-- Let $A \in \mathbb{K}^{n \times n}$ have the polar decomposition $A = UP$, and let
$\sigma_{\min}(A)$ be the smallest singular value of $A$. Then $P - \sigma_{\min}(A) I$ is
positive semidefinite, that is, $\sigma_{\min}(A) I \preceq P$ in the Loewner order.

The eigenvalues of $P$ are the values $\|Av\| = \|Pv\|$ at its unit eigenvectors $v$. The number
$\sigma_{\min}(A)$ is the infimum of `Matrix.colSingularValues A`. -/
theorem IsPolarDecomposition.posSemidef_sub_iInf_colSingularValues {A U P : Matrix n n 𝕜}
    (h : IsPolarDecomposition A U P) :
    (P - ((⨅ i, A.colSingularValues i : ℝ) : 𝕜) • 1).PosSemidef := by
  set c := ⨅ i, A.colSingularValues i
  have hP := h.isHermitian
  set V := (hP.eigenvectorUnitary : Matrix n n 𝕜)
  have hV : V ∈ unitaryGroup n 𝕜 := hP.eigenvectorUnitary.2
  have hVV : V * Vᴴ = 1 := mul_conjTranspose_self_of_mem_unitaryGroup hV
  have hspec : P = V * diagonal (fun i => ((hP.eigenvalues i : ℝ) : 𝕜)) * Vᴴ :=
    hP.eq_conj_diagonal
  have hc : ∀ i, c ≤ hP.eigenvalues i := by
    intro i
    have : Nonempty n := ⟨i⟩
    have h1 := A.iInf_colSingularValues_mul_norm_le (hP.eigenvectorBasis i)
    have h2 : ‖toEuclideanLin A (hP.eigenvectorBasis i)‖ = hP.eigenvalues i := by
      rw [toEuclideanLin_apply, h.eq_mul, ← mulVec_mulVec,
        norm_toLp_mulVec_of_mem_unitaryGroup h.mem_unitaryGroup, hP.mulVec_eigenvectorBasis,
        WithLp.toLp_smul, WithLp.toLp_ofLp, norm_smul, hP.eigenvectorBasis.orthonormal.1 i,
        mul_one, Real.norm_eq_abs, abs_of_nonneg (h.posSemidef.eigenvalues_nonneg i)]
    rw [hP.eigenvectorBasis.orthonormal.1 i, mul_one, h2] at h1
    exact h1
  have heq : P - (c : 𝕜) • 1
      = V * diagonal (fun i => ((hP.eigenvalues i - c : ℝ) : 𝕜)) * Vᴴ := by
    have hd : diagonal (fun i => ((hP.eigenvalues i - c : ℝ) : 𝕜))
        = diagonal (fun i => ((hP.eigenvalues i : ℝ) : 𝕜)) - (c : 𝕜) • 1 := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp only [Matrix.sub_apply, Matrix.smul_apply, diagonal_apply_eq, one_apply_eq,
            smul_eq_mul, mul_one]
        push_cast
        ring
      · simp only [Matrix.sub_apply, Matrix.smul_apply, diagonal_apply_ne _ hij, one_apply_ne hij,
          smul_zero, sub_zero]
    rw [hd, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hVV,
      ← hspec]
  rw [heq]
  refine (PosSemidef.diagonal fun i => ?_).mul_mul_conjTranspose_same V
  exact RCLike.ofReal_nonneg.2 (sub_nonneg.2 (hc i))

/-- **The perturbation of the unitary polar factor by the smallest singular values.** Let
$A, \tilde A \in \mathbb{K}^{n \times n}$ have polar decompositions $A = UP$ and
$\tilde A = \tilde U P'$, and suppose that $\sigma_{\min}(A) + \sigma_{\min}(\tilde A) > 0$.
Then
$$\|U - \tilde U\|_F
  \le \frac{2 \|A - \tilde A\|_F}{\sigma_{\min}(A) + \sigma_{\min}(\tilde A)}.$$
This is the complex form of the Li–Sun bound in [golub2013matrix], §9.4.3. The hypothesis holds,
for instance, when $A$ is nonsingular and $n \ge 1$.

The number $\sigma_{\min}(A)$ is the infimum of `Matrix.colSingularValues A`. -/
theorem IsPolarDecomposition.frobenius_norm_sub_le_div_iInf_colSingularValues
    {A Ã U Ũ P P' : Matrix n n 𝕜} (h : IsPolarDecomposition A U P)
    (h' : IsPolarDecomposition Ã Ũ P')
    (hσ : 0 < (⨅ i, A.colSingularValues i) + ⨅ i, Ã.colSingularValues i) :
    ‖U - Ũ‖ ≤ 2 * ‖A - Ã‖ / ((⨅ i, A.colSingularValues i) + ⨅ i, Ã.colSingularValues i) :=
  h.frobenius_norm_sub_le h' h.posSemidef_sub_iInf_colSingularValues
    h'.posSemidef_sub_iInf_colSingularValues hσ

end Perturbation

/-! ### The real Li–Sun bound -/

section RealPerturbation

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.Frobenius

omit [Fintype n] in
/-- If $P - bI + (b - a) uu^T$ is positive semidefinite, then $P$ is symmetric. -/
private theorem transpose_eq_of_posSemidef_pair {P : Matrix n n ℝ} {u : n → ℝ} {a b : ℝ}
    (hP : (P - b • 1 + (b - a) • vecMulVec u u).PosSemidef) : Pᵀ = P := by
  have h := hP.isHermitian.eq
  rw [conjTranspose_eq_transpose_of_trivial, transpose_add, transpose_sub, transpose_smul,
    transpose_smul, transpose_one, transpose_vecMulVec] at h
  simpa using h

/-- **A real Sylvester equation for $I - W$ with a rotation $W$.** Let
$P, Q, W, R \in \mathbb{R}^{n \times n}$, let $u, v \in \mathbb{R}^n$ be unit vectors, and let
$a \le b$ and $a' \le b'$ be real numbers with $a + b + a' + b' > 0$. Suppose that
$$P \succeq b (I - uu^T) + a\, uu^T, \qquad Q \succeq b' (I - vv^T) + a'\, vv^T$$
in the Loewner order, that $W^T W = I$ and $\det W = 1$, and that $P(I - W) + (I - W) Q = R$.
Then
$$\|I - W\|_F \le \frac{2 \|R\|_F}{a + b + a' + b'}.$$
This is the step behind the real Li–Sun bound.

The lower bounds are the hypotheses of `Matrix.le_trace_mul_one_sub`, written as `(P - b • 1 +
(b - a) • vecMulVec u u).PosSemidef`. With $X = I - W$, the identity $X X^T = X^T X = X + X^T$
gives $\operatorname{tr}(X^T R) = 2 \operatorname{tr}(PX) + 2 \operatorname{tr}(QX) \ge (a + b +
a' + b') \operatorname{tr} X = \frac{a + b + a' + b'}{2} \|X\|_F^2$. -/
theorem frobenius_norm_one_sub_le_of_mul_add_mul_eq {P Q W R : Matrix n n ℝ} {u v : n → ℝ}
    {a b a' b' : ℝ} (hab : a ≤ b) (hu : u ⬝ᵥ u = 1)
    (hP : (P - b • 1 + (b - a) • vecMulVec u u).PosSemidef) (hab' : a' ≤ b')
    (hv : v ⬝ᵥ v = 1) (hQ : (Q - b' • 1 + (b' - a') • vecMulVec v v).PosSemidef)
    (hW : Wᵀ * W = 1) (hdet : W.det = 1) (hs : 0 < a + b + a' + b')
    (h : P * (1 - W) + (1 - W) * Q = R) : ‖1 - W‖ ≤ 2 * ‖R‖ / (a + b + a' + b') := by
  have hW' : W * Wᵀ = 1 := mul_eq_one_comm.1 hW
  have hPt := transpose_eq_of_posSemidef_pair hP
  have hQt := transpose_eq_of_posSemidef_pair hQ
  set X := 1 - W with hX
  have hXX : Xᵀ * X = X + Xᵀ := by
    rw [hX, transpose_sub, transpose_one, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hW]
    abel
  have hXX' : X * Xᵀ = X + Xᵀ := by
    rw [hX, transpose_sub, transpose_one, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hW']
    abel
  have hsymm : ∀ S : Matrix n n ℝ, Sᵀ = S → trace (S * Xᵀ) = trace (S * X) := fun S hS => by
    rw [← trace_transpose, transpose_mul, transpose_transpose, hS, trace_mul_comm]
  have hnorm : ‖X‖ ^ 2 = 2 * trace X := by
    have := frobenius_norm_sq_eq_trace (𝕜 := ℝ) X
    rw [conjTranspose_eq_transpose_of_trivial, hXX, trace_add, trace_transpose] at this
    simpa [two_mul] using this
  have hkey : trace (Xᵀ * R) = 2 * trace (P * X) + 2 * trace (Q * X) := by
    rw [← h, Matrix.mul_add, trace_add, trace_mul_comm Xᵀ, Matrix.mul_assoc, hXX',
      ← Matrix.mul_assoc, hXX, trace_mul_comm (X + Xᵀ), Matrix.mul_add, Matrix.mul_add, trace_add,
      trace_add, hsymm P hPt, hsymm Q hQt]
    ring
  have hSO : W ∈ specialOrthogonalGroup n ℝ :=
    mem_specialOrthogonalGroup_iff.2 ⟨(mem_orthogonalGroup_iff' n ℝ).2 hW, hdet⟩
  have h1 := le_trace_mul_one_sub hab hu hP hSO
  have h2 := le_trace_mul_one_sub hab' hv hQ hSO
  have h3 := re_trace_conjTranspose_mul_le X R
  rw [conjTranspose_eq_transpose_of_trivial, RCLike.re_to_real] at h3
  rw [le_div_iff₀ hs]
  rcases (norm_nonneg X).eq_or_lt with hX0 | hX0
  · rw [← hX0, zero_mul]
    positivity
  · refine le_of_mul_le_mul_right ?_ hX0
    nlinarith

/-- **The real Li–Sun bound, in Loewner form.** Let $A, \tilde A \in \mathbb{R}^{n \times n}$ have
polar decompositions $A = UP$ and $\tilde A = \tilde U P'$, with
$\det A \cdot \det \tilde A > 0$. Let $u, v \in \mathbb{R}^n$ be unit vectors, and let $a \le b$
and $a' \le b'$ be real numbers with $a + b + a' + b' > 0$, such that
$$P \succeq b (I - uu^T) + a\, uu^T, \qquad P' \succeq b' (I - vv^T) + a'\, vv^T$$
in the Loewner order. Then
$$\|U - \tilde U\|_F \le \frac{4 \|A - \tilde A\|_F}{a + b + a' + b'}.$$
One can take for $a \le b$ the two smallest singular values of $A$, and likewise for $\tilde A$;
see `Matrix.IsPolarDecomposition.exists_posSemidef_sub_sortedSingularValues`.

The determinant condition makes $W = U^T \tilde U$ a rotation, and $I - W = U^T (U - \tilde U)$
solves the Sylvester equation of `Matrix.frobenius_norm_one_sub_le_of_mul_add_mul_eq`. -/
theorem IsPolarDecomposition.frobenius_norm_sub_le_of_det_mul_pos {A Ã U Ũ P P' : Matrix n n ℝ}
    (h : IsPolarDecomposition A U P) (h' : IsPolarDecomposition Ã Ũ P')
    (hdet : 0 < A.det * Ã.det) {u v : n → ℝ} {a b a' b' : ℝ} (hab : a ≤ b) (hu : u ⬝ᵥ u = 1)
    (hP : (P - b • 1 + (b - a) • vecMulVec u u).PosSemidef) (hab' : a' ≤ b')
    (hv : v ⬝ᵥ v = 1) (hP' : (P' - b' • 1 + (b' - a') • vecMulVec v v).PosSemidef)
    (hs : 0 < a + b + a' + b') : ‖U - Ũ‖ ≤ 4 * ‖A - Ã‖ / (a + b + a' + b') := by
  obtain ⟨hX, hsyl, hR⟩ := h.sylvester h'
  have hUU : Uᵀ * U = 1 := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact h.conjTranspose_mul_self
  have hUU' : Ũᵀ * Ũ = 1 := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact h'.conjTranspose_mul_self
  have hUU'' : U * Uᵀ = 1 := mul_eq_one_comm.1 hUU
  set W := Uᵀ * Ũ with hWdef
  have hW : Wᵀ * W = 1 := by
    rw [hWdef, transpose_mul, transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc U,
      hUU'', Matrix.one_mul, hUU']
  have hdetW : W.det = 1 := by
    have hpos : 0 < U.det * Ũ.det := by
      have hP0 := h.posSemidef.det_nonneg
      have hP0' := h'.posSemidef.det_nonneg
      rw [h.eq_mul, h'.eq_mul, det_mul, det_mul] at hdet
      by_contra hneg
      push Not at hneg
      nlinarith [mul_nonneg hP0 hP0']
    have hsq : (U.det * Ũ.det) ^ 2 = 1 := by
      rw [mul_pow, det_sq_eq_one_of_mem_orthogonalGroup ((mem_orthogonalGroup_iff' n ℝ).2 hUU),
        det_sq_eq_one_of_mem_orthogonalGroup ((mem_orthogonalGroup_iff' n ℝ).2 hUU'), one_mul]
    rw [hWdef, det_mul, det_transpose]
    nlinarith
  have hXW : Uᴴ * (U - Ũ) = 1 - W := by
    rw [conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub, hUU]
  rw [hXW] at hX hsyl
  rw [← hX]
  calc ‖1 - W‖ ≤ 2 * ‖Uᴴ * (A - Ã) - (A - Ã)ᴴ * Ũ‖ / (a + b + a' + b') :=
        frobenius_norm_one_sub_le_of_mul_add_mul_eq hab hu hP hab' hv hP' hW hdetW hs hsyl
    _ ≤ 2 * (2 * ‖A - Ã‖) / (a + b + a' + b') := by gcongr
    _ = 4 * ‖A - Ã‖ / (a + b + a' + b') := by ring

/-- **The symmetric polar factor above its two smallest singular values.** Let
$A \in \mathbb{R}^{m \times m}$ with $m \ge 1$ have the polar decomposition $A = UP$, and let
$\sigma_0 \ge \sigma_1 \ge \dots \ge \sigma_{m-1}$ be the singular values of $A$. Then there is
a unit vector $u \in \mathbb{R}^m$ with
$$P \succeq \sigma_{m-2} (I - uu^T) + \sigma_{m-1}\, uu^T$$
in the Loewner order.

The singular values are `Matrix.sortedSingularValues A`, indexed from $0$. For $m = 1$ the index
$m - 2$ is the natural-number difference $0$, so $\sigma_{m-2} = \sigma_{m-1}$. The proof reads
the bound off an SVD $A = W \operatorname{diag}(\sigma) V^T$, for which
$P = V \operatorname{diag}(\sigma) V^T$ by `Matrix.IsSVD.isPolarDecomposition_of_square` and the
uniqueness of $P$, and it takes for $u$ a right singular vector of $A$ for $\sigma_{m-1}$. The
statement does not record this property of $u$. -/
theorem IsPolarDecomposition.exists_posSemidef_sub_sortedSingularValues {m : ℕ}
    {A U P : Matrix (Fin m) (Fin m) ℝ} (h : IsPolarDecomposition A U P) (hm : m ≠ 0) :
    ∃ u : Fin m → ℝ, u ⬝ᵥ u = 1 ∧
      (P - A.sortedSingularValues (m - 2) • 1 +
        (A.sortedSingularValues (m - 2) - A.sortedSingularValues (m - 1)) •
          vecMulVec u u).PosSemidef := by
  obtain ⟨W, σ, V, hs⟩ := exists_isSVD A
  have hp := hs.isPolarDecomposition_of_square
  have hVV : Vᵀ * V = 1 := by
    have := mem_unitaryGroup_iff'.1 hs.mem_unitaryGroup_right
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  have hVV' : V * Vᵀ = 1 := mul_eq_one_comm.1 hVV
  have hPeq : P = V * diagonal (fun i : Fin m => σ i) * Vᵀ := by
    rw [h.eq_cfcSqrt, ← hp.eq_cfcSqrt, conjTranspose_eq_transpose_of_trivial]
    rfl
  rw [← hs.singularValues_eq (by omega) (by omega), ← hs.singularValues_eq (by omega) (by omega)]
  set l : Fin m := ⟨m - 1, by omega⟩
  set c := σ (m - 2)
  set k := σ (m - 2) - σ (m - 1)
  refine ⟨fun i => V i l, ?_, ?_⟩
  · have := congrFun (congrFun hVV l) l
    simpa [Matrix.mul_apply, dotProduct] using this
  have hvv : vecMulVec (fun i => V i l) (fun i => V i l) =
      V * diagonal (Pi.single l 1) * Vᵀ := by
    ext i j
    rw [Matrix.mul_apply]
    simp [vecMulVec_apply, mul_diagonal, Pi.single_apply]
  set d : Fin m → ℝ := fun i => σ i - c + k * (Pi.single l 1 : Fin m → ℝ) i with hd
  have hdiag : diagonal d =
      diagonal (fun i : Fin m => σ i) - c • 1 + k • diagonal (Pi.single l 1) := by
    ext i j
    by_cases hij : i = j <;> simp [hd, hij]
  have heq : P - c • 1 + k • vecMulVec (fun i => V i l) (fun i => V i l) =
      V * diagonal d * Vᵀ := by
    rw [hPeq, hvv, hdiag]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, hVV']
  have hd0 : 0 ≤ d := fun i => by
    by_cases hi : i = l
    · subst hi
      change 0 ≤ σ (m - 1) - σ (m - 2) + (σ (m - 2) - σ (m - 1)) * (Pi.single l 1 : Fin m → ℝ) l
      rw [Pi.single_eq_same]
      linarith
    · have hi' : (i : ℕ) ≤ m - 2 := by
        have : (i : ℕ) ≠ m - 1 := fun h' => hi (Fin.ext h')
        omega
      change 0 ≤ σ i - σ (m - 2) + k * (Pi.single l 1 : Fin m → ℝ) i
      rw [Pi.single_eq_of_ne hi, mul_zero]
      linarith [hs.antitone hi']
  rw [heq]
  have := (PosSemidef.diagonal hd0).mul_mul_conjTranspose_same V
  rwa [conjTranspose_eq_transpose_of_trivial] at this

/-- **The Li–Sun perturbation bound for the orthogonal polar factor.** Let
$A, \tilde A \in \mathbb{R}^{m \times m}$ have polar decompositions $A = UP$ and
$\tilde A = \tilde U P'$, and suppose that $\det A \cdot \det \tilde A > 0$. Let
$\sigma_0 \ge \dots \ge \sigma_{m-1}$ be the singular values of $A$, and $\tilde \sigma_0 \ge
\dots \ge \tilde \sigma_{m-1}$ those of $\tilde A$. Then
$$\|U - \tilde U\|_F \le \frac{4 \|A - \tilde A\|_F}
  {\sigma_{m-2} + \sigma_{m-1} + \tilde \sigma_{m-2} + \tilde \sigma_{m-1}},$$
where the denominator is the sum of the two smallest singular values of each matrix.
[golub2013matrix], §9.4.3, quotes this bound from W. Li and W. Sun, SIAM J. Matrix Anal. Appl.
23 (2002) 1183–1193.

The determinant condition cannot be dropped: $A = \operatorname{diag}(1, \varepsilon)$ and
$\tilde A = \operatorname{diag}(1, -\varepsilon)$ have $\|U - \tilde U\|_F = 2$ and
$\|A - \tilde A\|_F = 2 \varepsilon$. Li and Sun assume $\|A - \tilde A\|_2 < \sigma_{m-1} +
\tilde \sigma_{m-1}$, which keeps the segment from $A$ to $\tilde A$ nonsingular and so implies
the determinant condition.

The singular values are `Matrix.sortedSingularValues`, indexed from $0$; for $m = 1$ the index
$m - 2$ is $0$. For $m = 0$ both sides are $0$. The proof, through
`Matrix.IsPolarDecomposition.frobenius_norm_sub_le_of_det_mul_pos`, is not that of Li and Sun:
with the rotation $W = U^T \tilde U$, the pairing inequality `Matrix.le_trace_mul_one_sub`
replaces their pairing of eigenvalues. -/
theorem frobenius_norm_polar_sub_le {m : ℕ} {A Ã U Ũ P P' : Matrix (Fin m) (Fin m) ℝ}
    (h : IsPolarDecomposition A U P) (h' : IsPolarDecomposition Ã Ũ P')
    (hdet : 0 < A.det * Ã.det) :
    ‖U - Ũ‖ ≤ 4 * ‖A - Ã‖ / (A.sortedSingularValues (m - 2) + A.sortedSingularValues (m - 1) +
      Ã.sortedSingularValues (m - 2) + Ã.sortedSingularValues (m - 1)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [show U - Ũ = 0 from Subsingleton.elim _ _, norm_zero]
    refine div_nonneg (by positivity) ?_
    linarith [A.sortedSingularValues_nonneg (0 - 2), A.sortedSingularValues_nonneg (0 - 1),
      Ã.sortedSingularValues_nonneg (0 - 2), Ã.sortedSingularValues_nonneg (0 - 1)]
  obtain ⟨u, hu, hP⟩ := h.exists_posSemidef_sub_sortedSingularValues hm.ne'
  obtain ⟨v, hv, hP'⟩ := h'.exists_posSemidef_sub_sortedSingularValues hm.ne'
  have hanti : ∀ B : Matrix (Fin m) (Fin m) ℝ,
      B.sortedSingularValues (m - 1) ≤ B.sortedSingularValues (m - 2) := fun B =>
    B.sortedSingularValues_antitone (by omega)
  have hA : A.det ≠ 0 := fun h0 => by rw [h0, zero_mul] at hdet; exact lt_irrefl 0 hdet
  have hpos : 0 < A.sortedSingularValues (m - 1) := by
    refine lt_of_le_of_ne (A.sortedSingularValues_nonneg _) (Ne.symm fun h0 => ?_)
    have hr := (A.sortedSingularValues_eq_zero_iff_rank_le (m - 1)).1 h0
    rw [rank_of_isUnit A ((isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.2 hA)),
      Fintype.card_fin] at hr
    omega
  have hs : 0 < A.sortedSingularValues (m - 1) + A.sortedSingularValues (m - 2) +
      Ã.sortedSingularValues (m - 1) + Ã.sortedSingularValues (m - 2) := by
    linarith [A.sortedSingularValues_nonneg (m - 2), Ã.sortedSingularValues_nonneg (m - 2),
      Ã.sortedSingularValues_nonneg (m - 1)]
  have key := h.frobenius_norm_sub_le_of_det_mul_pos h' hdet (hanti A) hu hP (hanti Ã) hv hP' hs
  convert key using 2
  ring

end RealPerturbation

/-! ### The sign of the Jordan–Wielandt matrix -/

section Sign

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The sign of the Jordan–Wielandt matrix.** Let $A \in \mathbb{C}^{n \times n}$ be nonsingular
with polar decomposition $A = UP$. Then
$$\operatorname{sign} \begin{bmatrix} 0 & A \\ A^H & 0 \end{bmatrix}
  = \begin{bmatrix} 0 & U \\ U^H & 0 \end{bmatrix}.$$
This is in [golub2013matrix], §9.4.3. [golub2013matrix] does not state that $A$ is nonsingular.
This hypothesis is needed so that no eigenvalue $\pm \sigma_i$ of the block matrix is $0$.

The block matrix is `Matrix.hermitianDilation Aᴴ`, which is `fromBlocks 0 A Aᴴ 0`, and the sign
is `Matrix.matrixSign`. Let $M = U P U^H$, which is positive definite, and $X = \begin{bmatrix}
I & I \\ -U^H & U^H \end{bmatrix}$, whose inverse is $\frac12 \begin{bmatrix} I & -U \\ I & U
\end{bmatrix}$. Then $X^{-1} \begin{bmatrix} 0 & A \\ A^H & 0 \end{bmatrix} X =
\operatorname{diag}(-M, M)$, and `Matrix.matrixSign_conj_fromBlocks` gives the sign $X
\operatorname{diag}(-I, I) X^{-1} = \begin{bmatrix} 0 & U \\ U^H & 0 \end{bmatrix}$. -/
theorem matrixSign_hermitianDilation {A U P : Matrix n n ℂ} (hA : IsUnit A)
    (h : IsPolarDecomposition A U P) :
    matrixSign (hermitianDilation Aᴴ) = hermitianDilation Uᴴ := by
  have hUU : Uᴴ * U = 1 := h.conjTranspose_mul_self
  have hUU' : U * Uᴴ = 1 := mul_eq_one_comm.1 hUU
  have hUhu : IsUnit Uᴴ := (isUnit_iff_isUnit_det _).2 (isUnit_det_of_right_inverse hUU)
  have hAh : Aᴴ = P * Uᴴ := by
    rw [h.eq_mul, conjTranspose_mul, h.isHermitian.eq]
  -- the positive definite matrix `M = U P Uᴴ = A Uᴴ`
  set M := U * P * Uᴴ with hMdef
  have hP : P.PosDef := h.posSemidef.posDef_iff_isUnit.2 (h.isUnit hA)
  have hM : M.PosDef := by
    have := hP.conjTranspose_mul_mul_same (mulVec_injective_of_isUnit hUhu)
    rwa [conjTranspose_conjTranspose] at this
  have hAU : A * Uᴴ = M := by rw [h.eq_mul]
  have hUM : Uᴴ * M = P * Uᴴ := by
    rw [hMdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
  -- the eigenvector matrix `X` and its inverse
  set X : Matrix (n ⊕ n) (n ⊕ n) ℂ := fromBlocks 1 1 (-Uᴴ) Uᴴ with hXdef
  set Y : Matrix (n ⊕ n) (n ⊕ n) ℂ := (2 : ℂ)⁻¹ • fromBlocks 1 (-U) 1 U with hYdef
  have hYX : Y * X = 1 := by
    rw [hYdef, hXdef, Matrix.smul_mul, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_smul]
    simp only [Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg, neg_neg, hUU']
    congr 1 <;> [skip; simp; simp; skip] <;>
      rw [← two_smul ℂ (1 : Matrix n n ℂ), smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
  have hXinv : X⁻¹ = Y := inv_eq_left_inv hYX
  have hXu : IsUnit X := (isUnit_iff_isUnit_det _).2 (isUnit_det_of_left_inverse hYX)
  -- `H X = X diag(−M, M)`
  have hH : hermitianDilation Aᴴ = fromBlocks 0 A Aᴴ 0 := by
    rw [hermitianDilation, conjTranspose_conjTranspose]
  have hHX : fromBlocks 0 A Aᴴ 0 * X = X * fromBlocks (-M) 0 0 M := by
    rw [hXdef, fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, zero_add,
      add_zero, Matrix.mul_neg, Matrix.neg_mul, neg_neg, neg_zero, hAU, hUM, hAh]
  have hconj : X⁻¹ * hermitianDilation Aᴴ * X =
      reindex (Equiv.refl _) (Equiv.refl _) (fromBlocks (-M) 0 0 M) := by
    rw [reindex_refl_refl, hH, Matrix.mul_assoc, hHX, ← Matrix.mul_assoc,
      nonsing_inv_mul _ ((isUnit_iff_isUnit_det X).1 hXu), Matrix.one_mul]
  have hneg : ∀ μ ∈ spectrum ℂ (-M), μ.re < 0 := fun μ hμ => by
    rw [← spectrum.neg_eq, Set.mem_neg] at hμ
    have := hM.re_pos_of_mem_spectrum hμ
    rw [Complex.neg_re] at this
    linarith
  rw [matrixSign_conj_fromBlocks (Equiv.refl _) hXu hconj hneg
    fun μ hμ => hM.re_pos_of_mem_spectrum hμ, reindex_refl_refl, hXinv, hYdef,
    Matrix.mul_smul, hXdef, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_smul,
    hermitianDilation, conjTranspose_conjTranspose]
  simp only [Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, zero_add, add_zero, Matrix.mul_neg,
    Matrix.neg_mul, neg_neg, hUU, neg_add_cancel]
  congr 1 <;> [simp; skip; skip; simp] <;>
    rw [← two_smul ℂ, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

end Sign

end Matrix
