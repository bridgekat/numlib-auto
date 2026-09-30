/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.UnitaryGroup` (real orthogonal matrices).
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Trace inequalities for unitary and real orthogonal matrices

* `Matrix.re_trace_mul_le_trace_of_posSemidef`: a unitary factor does not increase the real trace
  of a positive semidefinite matrix, `re tr(W P) ≤ re tr P`.

Facts about a real matrix `O` with `Oᵀ O = 1`:

* `Matrix.det_sq_eq_one_of_transpose_mul_self`: `(det O)² = 1`.
* `Matrix.PosSemidef.trace_mul_le_trace`: the real case of the first item, `tr(R O) ≤ tr R`.
* `Matrix.trace_le_card_sub_two_of_det_eq_neg_one`: an improper orthogonal matrix
  (`det O = -1`) has `tr O ≤ n - 2`.
* `Matrix.trace_mul_one_sub_ge`: for a rotation `W` and a symmetric `P ⪰ b (1 - u uᵀ) + a u uᵀ`
  (`u` a unit vector, `a ≤ b`), `tr(P (1 - W)) ≥ (a + b)/2 · tr(1 - W)`.

They are the trace estimates behind the orthogonal Procrustes problem
(`Numlib/LinearAlgebra/Matrix/Procrustes`) and the real Li–Sun perturbation bound for the
orthogonal polar factor (`Numlib/Analysis/Matrix/Function/Polar`).
-/

open scoped ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The determinant of a real orthogonal matrix is `±1`: its square is `1`. -/
theorem det_sq_eq_one_of_transpose_mul_self {O : Matrix n n ℝ} (hO : Oᵀ * O = 1) :
    O.det ^ 2 = 1 := by
  have := congrArg det hO
  rw [det_mul, det_transpose, det_one] at this
  rw [sq]; exact this

/-- **A unitary factor does not increase the real trace of a positive semidefinite matrix**:
`re tr(W P) ≤ re tr P` for `W` unitary and `P ⪰ 0` — the step "`tr(ZΣ) = ∑ z_ii σ_i ≤ ∑ σ_i`" of
[golub2013matrix] §6.4.1 in polar form. In an eigenbasis of `P`, `tr(W P) = ∑ z_ii λ_i` with
`Z` unitary, so `|z_ii| ≤ 1`, and `λ_i ≥ 0`. -/
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

/-- The trace of a positive semidefinite matrix is not increased by an orthogonal factor:
`tr(R O) ≤ tr R`, the real case of `Matrix.re_trace_mul_le_trace_of_posSemidef`. -/
theorem PosSemidef.trace_mul_le_trace {R O : Matrix n n ℝ} (hR : R.PosSemidef)
    (hO : Oᵀ * O = 1) : trace (R * O) ≤ trace R := by
  have h := re_trace_mul_le_trace_of_posSemidef ((mem_orthogonalGroup_iff' n ℝ).2 hO) hR
  rwa [RCLike.re_to_real, RCLike.re_to_real, trace_mul_comm] at h

/-- An improper orthogonal matrix has trace at most `n - 2`: `-1` is an eigenvalue
(`det(O + 1) = det O det(1 + Oᵀ) = -det(O + 1)`), and on the orthogonal complement of its
eigenvector the trace is at most the dimension (`Matrix.PosSemidef.trace_mul_le_trace`). -/
theorem trace_le_card_sub_two_of_det_eq_neg_one {O : Matrix n n ℝ} (hO : Oᵀ * O = 1)
    (hdet : O.det = -1) : trace O ≤ Fintype.card n - 2 := by
  have hO' : O * Oᵀ = 1 := mul_eq_one_comm.1 hO
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

/-- **The pairing inequality** behind the real Li–Sun bound: if `W` is a rotation (`Wᵀ W = 1`,
`det W = 1`) and the symmetric `P` satisfies `P ⪰ b (1 - u uᵀ) + a u uᵀ` for a unit vector `u` and
`a ≤ b` (for instance `a`, `b` the two smallest eigenvalues of `P`), then
`tr(P (1 - W)) ≥ (a + b)/2 · tr(1 - W)`. Write `P - (a + b)/2 = R₀ + (b - a)/2 · H` with `R₀ ⪰ 0`
and the reflection `H = 1 - 2 u uᵀ`: `tr(R₀ (1 - W)) ≥ 0` because `W` is orthogonal
(`Matrix.PosSemidef.trace_mul_le_trace`), and `tr(H (1 - W)) = n - 2 - tr(H W) ≥ 0` because `H W`
is an improper orthogonal matrix (`Matrix.trace_le_card_sub_two_of_det_eq_neg_one`). -/
theorem trace_mul_one_sub_ge {P W : Matrix n n ℝ} {u : n → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hu : u ⬝ᵥ u = 1) (hP : (P - b • 1 + (b - a) • vecMulVec u u).PosSemidef)
    (hW : Wᵀ * W = 1) (hdet : W.det = 1) :
    (a + b) / 2 * trace (1 - W) ≤ trace (P * (1 - W)) := by
  set R₀ := P - b • 1 + (b - a) • vecMulVec u u with hR₀
  set H := 1 - (2 : ℝ) • vecMulVec u u with hH
  have hHt : Hᵀ = H := by
    rw [hH, transpose_sub, transpose_one, transpose_smul, transpose_vecMulVec]
  have hHH : Hᵀ * H = 1 := by
    rw [hHt, hH, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, vecMulVec_mul_vecMulVec, hu,
      one_smul]
    module
  have hdetH : H.det = -1 := by
    have e : H = 1 + replicateCol Unit (-(2 : ℝ) • u) * replicateRow Unit u := by
      rw [hH, ← vecMulVec_eq, smul_vecMulVec, neg_smul, sub_eq_add_neg]
    rw [e, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, dotProduct_comm, hu]
    norm_num
  have hHW : (H * W)ᵀ * (H * W) = 1 := by
    rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Hᵀ, hHH, Matrix.one_mul, hW]
  have h1 : trace (R₀ * W) ≤ trace R₀ := hP.trace_mul_le_trace hW
  have h2 := trace_le_card_sub_two_of_det_eq_neg_one hHW (by rw [det_mul, hdetH, hdet]; ring)
  have htu : trace (vecMulVec u u) = 1 := by rw [trace_vecMulVec, hu]
  have hPe : P = R₀ + b • 1 - (b - a) • vecMulVec u u := by rw [hR₀]; abel
  have e1 : trace (P * (1 - W)) = (trace R₀ - trace (R₀ * W)) + b * trace (1 - W)
      - (b - a) * (trace (vecMulVec u u) - trace (vecMulVec u u * W)) := by
    rw [hPe]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_one, trace_add, trace_sub, trace_smul, smul_eq_mul]
    ring
  have e2 : trace (H * W) = trace W - 2 * trace (vecMulVec u u * W) := by
    rw [hH, Matrix.sub_mul, Matrix.one_mul, trace_sub, Matrix.smul_mul, trace_smul, smul_eq_mul]
  have e3 : trace (1 - W) = Fintype.card n - trace W := by rw [trace_sub, trace_one]
  rw [e1, e3, htu]
  rw [e2] at h2
  nlinarith [mul_nonneg (sub_nonneg.2 hab)
    (show 0 ≤ (Fintype.card n - trace W) - 2 * (1 - trace (vecMulVec u u * W)) by linarith)]

end Matrix
