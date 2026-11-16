/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.UnitaryGroup` (real orthogonal matrices).
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Numlib.LinearAlgebra.Matrix.QR

/-!
# Trace inequalities for unitary and orthogonal matrices

This file proves trace inequalities for unitary and real orthogonal matrices. A unitary factor $W$
does not increase the real part of the trace of a positive semidefinite matrix $P$:
$\operatorname{Re} \operatorname{tr}(WP) \le \operatorname{Re} \operatorname{tr} P$. For a real
orthogonal matrix $O \in O(n)$, $(\det O)^2 = 1$, and an improper orthogonal matrix ($\det O = -1$)
has $\operatorname{tr} O \le n - 2$. These facts combine into a pairing inequality for a rotation
$W \in SO(n)$. They are the trace estimates behind the orthogonal Procrustes problem
(`Numlib.LinearAlgebra.Matrix.Procrustes`) and the real Li–Sun perturbation bound for the orthogonal
polar factor (`Numlib.Analysis.Matrix.Function.Polar`).

## Main results

* `Matrix.re_trace_mul_le_trace_of_posSemidef`: $\operatorname{Re} \operatorname{tr}(WP) \le
  \operatorname{Re} \operatorname{tr} P$ for $W$ unitary and $P$ positive semidefinite.
* `Matrix.det_sq_eq_one_of_mem_orthogonalGroup`: $(\det O)^2 = 1$ for an orthogonal matrix $O$ over
  any commutative ring.
* `Matrix.PosSemidef.trace_mul_le_trace`: $\operatorname{tr}(RO) \le \operatorname{tr} R$ for $R$
  real positive semidefinite and $O$ orthogonal.
* `Matrix.trace_le_card_sub_two_of_det_eq_neg_one`: an orthogonal matrix $O$ with $\det O = -1$ has
  $\operatorname{tr} O \le n - 2$.
* `Matrix.le_trace_mul_one_sub`: for $W \in SO(n)$, a unit vector $u$, $a \le b$ and
  $P \succeq b(I - uu^T) + a uu^T$, the inequality $\frac{a + b}{2} \operatorname{tr}(I - W) \le
  \operatorname{tr}(P(I - W))$ holds.
-/

open scoped ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Let $R$ be a commutative ring and let $O \in R^{n \times n}$ be orthogonal, $O^T O = I$. Then
$(\det O)^2 = 1$. -/
theorem det_sq_eq_one_of_mem_orthogonalGroup {R : Type*} [CommRing R] {O : Matrix n n R}
    (hO : O ∈ orthogonalGroup n R) : O.det ^ 2 = 1 := by
  have := congrArg det ((mem_orthogonalGroup_iff' n R).1 hO)
  rw [det_mul, det_transpose, det_one] at this
  rw [sq]; exact this

/-- **A unitary factor does not increase the real trace of a positive semidefinite matrix.** Let
$\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let $W \in \mathbb{K}^{n \times n}$ be unitary and
let $P \in \mathbb{K}^{n \times n}$ be positive semidefinite. Then $$\operatorname{Re}
\operatorname{tr}(WP) \le \operatorname{Re} \operatorname{tr} P.$$

This is the step "$\operatorname{tr}(Z\Sigma) = \sum z_{ii} \sigma_i \le \sum \sigma_i$" of
[golub2013matrix], §6.4.1, in polar form. In an eigenbasis of $P$, $\operatorname{tr}(WP) =
\sum_i z_{ii} \lambda_i$ with $Z$ unitary, so $|z_{ii}| \le 1$, and $\lambda_i \ge 0$. -/
theorem re_trace_mul_le_trace_of_posSemidef {𝕜 : Type*} [RCLike 𝕜] {W : Matrix n n 𝕜}
    (hW : W ∈ unitaryGroup n 𝕜) {P : Matrix n n 𝕜} (hP : P.PosSemidef) :
    RCLike.re (trace (W * P)) ≤ RCLike.re (trace P) := by
  set u := hP.isHermitian.eigenvectorUnitary
  set d := hP.isHermitian.eigenvalues
  set D : Matrix n n 𝕜 := diagonal (RCLike.ofReal ∘ d)
  have hPd : P = (u : Matrix n n 𝕜) * D * star (u : Matrix n n 𝕜) := by
    conv_lhs => rw [hP.isHermitian.spectral_theorem]
    rfl
  have huu : star (u : Matrix n n 𝕜) * u = 1 := Unitary.coe_star_mul_self u
  set Z := star (u : Matrix n n 𝕜) * W * (u : Matrix n n 𝕜)
  have hZ : Z ∈ unitaryGroup n 𝕜 := mul_mem (mul_mem (Unitary.star_mem u.2) hW) u.2
  have h1 : trace (W * P) = trace (Z * D) := by
    calc trace (W * P) = trace ((W * (u : Matrix n n 𝕜) * D) * star (u : Matrix n n 𝕜)) := by
          rw [hPd]; simp only [Matrix.mul_assoc]
      _ = trace (star (u : Matrix n n 𝕜) * (W * (u : Matrix n n 𝕜) * D)) :=
          trace_mul_comm _ _
      _ = trace (Z * D) := by simp only [Z, Matrix.mul_assoc]
  have h2 : trace P = trace D := by
    calc trace P = trace (((u : Matrix n n 𝕜) * D) * star (u : Matrix n n 𝕜)) := by rw [hPd]
      _ = trace (star (u : Matrix n n 𝕜) * ((u : Matrix n n 𝕜) * D)) := trace_mul_comm _ _
      _ = trace D := by rw [← Matrix.mul_assoc, huu, Matrix.one_mul]
  rw [h1, h2, trace, trace, map_sum, map_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [diag_apply, mul_diagonal, D, diagonal_apply_eq, Function.comp_apply]
  rw [mul_comm, RCLike.re_ofReal_mul, RCLike.ofReal_re]
  calc d i * RCLike.re (Z i i) ≤ d i * 1 :=
        mul_le_mul_of_nonneg_left ((RCLike.re_le_norm _).trans
          (entry_norm_bound_of_unitary hZ i i)) (hP.eigenvalues_nonneg i)
    _ = d i := mul_one _

/-- Let $R \in \mathbb{R}^{n \times n}$ be positive semidefinite and let
$O \in \mathbb{R}^{n \times n}$ be orthogonal. Then
$\operatorname{tr}(RO) \le \operatorname{tr} R$. This is the real case of
`Matrix.re_trace_mul_le_trace_of_posSemidef`. -/
theorem PosSemidef.trace_mul_le_trace {R O : Matrix n n ℝ} (hR : R.PosSemidef)
    (hO : O ∈ orthogonalGroup n ℝ) : trace (R * O) ≤ trace R := by
  have h := re_trace_mul_le_trace_of_posSemidef hO hR
  rwa [RCLike.re_to_real, RCLike.re_to_real, trace_mul_comm] at h

/-- Let $O \in \mathbb{R}^{n \times n}$ be orthogonal with $\det O = -1$. Then
$\operatorname{tr} O \le n - 2$.

The proof shows that $-1$ is an eigenvalue, because $\det(O + I) = \det O \det(I + O^T) =
-\det(O + I)$. On the orthogonal complement of its eigenvector, the trace is at most the
dimension (`Matrix.PosSemidef.trace_mul_le_trace`). -/
theorem trace_le_card_sub_two_of_det_eq_neg_one {O : Matrix n n ℝ}
    (hO : O ∈ orthogonalGroup n ℝ) (hdet : O.det = -1) : trace O ≤ Fintype.card n - 2 := by
  have hO' : O * Oᵀ = 1 := (mem_orthogonalGroup_iff n ℝ).1 hO
  have hdet0 : (O + 1).det = 0 := by
    have e : O + 1 = O * (O + 1)ᵀ := by
      rw [transpose_add, transpose_one, Matrix.mul_add, hO', Matrix.mul_one, add_comm]
    have := congrArg det e
    rw [det_mul, det_transpose, hdet] at this
    linarith
  obtain ⟨x, hx0, hx⟩ := exists_mulVec_eq_zero_iff.2 hdet0
  have hOx : O *ᵥ x = -x := by
    rw [add_mulVec, one_mulVec] at hx
    exact eq_neg_of_add_eq_zero_left hx
  set c := x ⬝ᵥ x with hcdef
  have hc : c ≠ 0 := fun h0 => hx0 (dotProduct_self_eq_zero.1 h0)
  set Pr := 1 - c⁻¹ • vecMulVec x x with hPr
  have hPrt : Prᵀ = Pr := by
    rw [hPr, transpose_sub, transpose_one, transpose_smul, transpose_vecMulVec]
  have hPrPr : Pr * Pr = Pr := by
    rw [hPr, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, vecMulVec_mul_vecMulVec,
      vecMulVec_smul, ← hcdef, smul_smul]
    rw [show c⁻¹ * c⁻¹ * c = c⁻¹ by field_simp]
    abel
  have hPrpsd : Pr.PosSemidef := by
    have := posSemidef_conjTranspose_mul_self Pr
    rwa [conjTranspose_eq_transpose_of_trivial, hPrt, hPrPr] at this
  have h1 := hPrpsd.trace_mul_le_trace hO
  have htPr : trace Pr = Fintype.card n - 1 := by
    rw [hPr, trace_sub, trace_one, trace_smul, trace_vecMulVec, ← hcdef, smul_eq_mul,
      inv_mul_cancel₀ hc]
  have htPrO : trace (Pr * O) = trace O + 1 := by
    rw [hPr, Matrix.sub_mul, Matrix.one_mul, trace_sub, Matrix.smul_mul, trace_smul,
      trace_mul_comm, mul_vecMulVec, hOx, trace_vecMulVec, neg_dotProduct, ← hcdef,
      smul_eq_mul, mul_neg, inv_mul_cancel₀ hc]
    ring
  rw [htPr, htPrO] at h1
  linarith

/-- The **pairing inequality** behind the real Li–Sun bound. Let $P, W \in \mathbb{R}^{n \times n}$,
let $u \in \mathbb{R}^n$ be a unit vector, $u^T u = 1$, and let $a \le b$ be real numbers. Let
$W$ be a rotation, $W \in SO(n)$, and let $$P - b(I - uu^T) - a\, uu^T$$ be positive
semidefinite (so $P$ is symmetric). Then $$\frac{a + b}{2} \operatorname{tr}(I - W) \le
\operatorname{tr}(P(I - W)).$$ For instance, $a$ and $b$ can be the two smallest eigenvalues of
$P$.

The proof writes $P - \frac{a + b}{2} I = R_0 + \frac{b - a}{2} H$ with $R_0 \succeq 0$ and the
reflection $H = I - 2uu^T$ (`Matrix.householder u`), of determinant $-1$. Then
$\operatorname{tr}(R_0 (I - W)) \ge 0$ because $W$ is orthogonal
(`Matrix.PosSemidef.trace_mul_le_trace`), and $\operatorname{tr}(H(I - W)) = n - 2 -
\operatorname{tr}(HW) \ge 0$ because $HW$ is an improper orthogonal matrix
(`Matrix.trace_le_card_sub_two_of_det_eq_neg_one`). In Lean the hypothesis on $P$ is that
`P - b • 1 + (b - a) • vecMulVec u u` is positive semidefinite. -/
theorem le_trace_mul_one_sub {P W : Matrix n n ℝ} {u : n → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hu : u ⬝ᵥ u = 1) (hP : (P - b • 1 + (b - a) • vecMulVec u u).PosSemidef)
    (hW : W ∈ specialOrthogonalGroup n ℝ) :
    (a + b) / 2 * trace (1 - W) ≤ trace (P * (1 - W)) := by
  obtain ⟨hWO, hdet⟩ := mem_specialOrthogonalGroup_iff.1 hW
  set R₀ := P - b • 1 + (b - a) • vecMulVec u u with hR₀
  have hu' : star u ⬝ᵥ u = 1 := by rwa [star_trivial]
  set H := householder u with hH
  have hHO : H ∈ orthogonalGroup n ℝ := householder_mem_unitaryGroup hu'
  have hH' : H = 1 - (2 : ℝ) • vecMulVec u u := by rw [hH, householder, star_trivial]
  have h1 : trace (R₀ * W) ≤ trace R₀ := hP.trace_mul_le_trace hWO
  have h2 := trace_le_card_sub_two_of_det_eq_neg_one (mul_mem hHO hWO)
    (by rw [det_mul, det_householder hu', hdet]; ring)
  have htu : trace (vecMulVec u u) = 1 := by rw [trace_vecMulVec, hu]
  have hPe : P = R₀ + b • 1 - (b - a) • vecMulVec u u := by rw [hR₀]; abel
  have e1 : trace (P * (1 - W)) = (trace R₀ - trace (R₀ * W)) + b * trace (1 - W)
      - (b - a) * (trace (vecMulVec u u) - trace (vecMulVec u u * W)) := by
    rw [hPe]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_one, trace_add, trace_sub, trace_smul, smul_eq_mul]
    ring
  have e2 : trace (H * W) = trace W - 2 * trace (vecMulVec u u * W) := by
    rw [hH', Matrix.sub_mul, Matrix.one_mul, trace_sub, Matrix.smul_mul, trace_smul, smul_eq_mul]
  have e3 : trace (1 - W) = Fintype.card n - trace W := by rw [trace_sub, trace_one]
  rw [e1, e3, htu]
  rw [e2] at h2
  nlinarith [mul_nonneg (sub_nonneg.2 hab)
    (show 0 ≤ (Fintype.card n - trace W) - 2 * (1 - trace (vecMulVec u u * W)) by linarith)]

end Matrix
