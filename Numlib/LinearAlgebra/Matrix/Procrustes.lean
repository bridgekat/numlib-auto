/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Matrix`, beside the polar decomposition.
-/
import Numlib.LinearAlgebra.Matrix.OrthogonalGroup
import Numlib.LinearAlgebra.Matrix.Polar

/-!
# The orthogonal Procrustes problem

Given `A B : Matrix m p 𝕜`, find a unitary `Q` minimizing the Frobenius norm `‖A − B Q‖_F`
([golub2013matrix] §6.4.1, after Green 1952 and Schönemann 1966). Expanding the norm reduces the
problem to maximizing `re tr(Qᴴ Bᴴ A)`, and if `Bᴴ A = Q₀ P` is a polar decomposition then
`re tr(Qᴴ Q₀ P) ≤ re tr P` for every unitary `Q`, with equality at `Q = Q₀`: the unitary polar
factor of `Bᴴ A` solves the problem. The book's solution `Q = U Vᴴ` from an SVD `Uᴴ (Bᴴ A) V = Σ`
is that polar factor (`Matrix.IsSVD.isPolarDecomposition_of_square`).

## Main results

* `Matrix.frobenius_norm_sub_mul_sq`: `‖A − B Q‖² = ‖A‖² + ‖B‖² − 2 re tr(Qᴴ Bᴴ A)`.
* `Matrix.frobenius_norm_sub_mul_le_of_isPolarDecomposition`: the Procrustes theorem, polar
  form; `Matrix.frobenius_norm_sub_mul_le_of_isSVD` is the book's SVD form.
* `Matrix.re_trace_mul_le_sum_colSingularValues`: `re tr(Q C) ≤ ∑ σ_i(C)` for unitary `Q`, with
  equality at `Q = V Uᴴ` for an SVD `Uᴴ C V = Σ`
  (`Matrix.IsSVD.re_trace_mul_eq_sum`).

## Implementation notes

The Frobenius norm is Mathlib's scoped `Matrix.Norms.Frobenius` instance, as in
`Numlib/Analysis/Matrix/OperatorNorm`. The index types are arbitrary finite types, except where an
SVD (which is `Fin`-indexed) appears.

## References

* [golub2013matrix] §6.4.1.
-/

open scoped ComplexOrder Matrix.Norms.Frobenius

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {m p : Type*} [Fintype m] [Fintype p]
  [DecidableEq p]

/-- **The Procrustes expansion** ([golub2013matrix] §6.4.1): for unitary `Q`,
`‖A − B Q‖_F² = ‖A‖_F² + ‖B‖_F² − 2 re tr(Qᴴ Bᴴ A)`. -/
theorem frobenius_norm_sub_mul_sq {Q : Matrix p p 𝕜} (hQ : Q ∈ unitaryGroup p 𝕜)
    (A B : Matrix m p 𝕜) :
    ‖A - B * Q‖ ^ 2 = ‖A‖ ^ 2 + ‖B‖ ^ 2 - 2 * RCLike.re (trace (Qᴴ * Bᴴ * A)) := by
  classical
  rw [show Qᴴ * Bᴴ * A = (B * Q)ᴴ * A by rw [conjTranspose_mul]]
  have hBQ : ‖B * Q‖ = ‖B‖ := by
    simpa using frobenius_norm_unitary_mul_mul_unitary (one_mem _) B hQ
  have h := frobenius_norm_sq_eq_trace (A - B * Q)
  have hA := frobenius_norm_sq_eq_trace A
  have hB := frobenius_norm_sq_eq_trace (B * Q)
  rw [hBQ] at hB
  have hexp : (A - B * Q)ᴴ * (A - B * Q)
      = Aᴴ * A - ((B * Q)ᴴ * A)ᴴ - (B * Q)ᴴ * A + (B * Q)ᴴ * (B * Q) := by
    rw [show ((B * Q)ᴴ * A)ᴴ = Aᴴ * (B * Q) by
      rw [conjTranspose_mul, conjTranspose_conjTranspose]]
    simp only [conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [hexp, trace_add, trace_sub, trace_sub, trace_conjTranspose, ← hA, ← hB] at h
  have h' := congrArg RCLike.re h
  simp only [RCLike.ofReal_re, map_add, map_sub, RCLike.star_def, RCLike.conj_re] at h'
  linarith

/-- **The orthogonal Procrustes theorem, polar form** ([golub2013matrix] §6.4.1): if `Bᴴ A = Q₀ P`
is a polar decomposition, then `Q₀` is unitary and minimizes `‖A − B Q‖_F` over unitary `Q`. -/
theorem frobenius_norm_sub_mul_le_of_isPolarDecomposition {A B : Matrix m p 𝕜}
    {Q₀ P : Matrix p p 𝕜} (h : IsPolarDecomposition (Bᴴ * A) Q₀ P) :
    Q₀ ∈ unitaryGroup p 𝕜 ∧ ∀ Q ∈ unitaryGroup p 𝕜, ‖A - B * Q₀‖ ≤ ‖A - B * Q‖ := by
  have hQ₀ := h.mem_unitaryGroup
  refine ⟨hQ₀, fun Q hQ => ?_⟩
  have htr : ∀ X : Matrix p p 𝕜, trace (Xᴴ * Bᴴ * A) = trace ((Xᴴ * Q₀) * P) := fun X => by
    rw [Matrix.mul_assoc, h.eq_mul, Matrix.mul_assoc]
  have hWu : Qᴴ * Q₀ ∈ unitaryGroup p 𝕜 := by
    rw [← star_eq_conjTranspose]; exact mul_mem (Unitary.star_mem hQ) hQ₀
  have hle : RCLike.re (trace (Qᴴ * Bᴴ * A)) ≤ RCLike.re (trace (Q₀ᴴ * Bᴴ * A)) := by
    rw [htr, htr, h.conjTranspose_mul_self, Matrix.one_mul]
    exact re_trace_mul_le_trace_of_posSemidef hWu h.posSemidef
  have hsq : ‖A - B * Q₀‖ ^ 2 ≤ ‖A - B * Q‖ ^ 2 := by
    rw [frobenius_norm_sub_mul_sq hQ₀, frobenius_norm_sub_mul_sq hQ]
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

/-- **The orthogonal Procrustes theorem, the book's form** ([golub2013matrix] §6.4.1, "The upper
bound is clearly attained by setting `Z = I_p`, i.e., `Q = UVᵀ`", Algorithm 6.4.1): if
`Uᴴ (Bᴴ A) V = Σ` is an SVD, then `Q₀ = U Vᴴ` is unitary and minimizes `‖A − B Q‖_F` over unitary
`Q`. -/
theorem frobenius_norm_sub_mul_le_of_isSVD {n : ℕ} {A B : Matrix m (Fin n) 𝕜}
    {U V : Matrix (Fin n) (Fin n) 𝕜} {σ : ℕ → ℝ} (h : IsSVD (Bᴴ * A) U σ V) :
    U * Vᴴ ∈ unitaryGroup (Fin n) 𝕜 ∧
      ∀ Q ∈ unitaryGroup (Fin n) 𝕜, ‖A - B * (U * Vᴴ)‖ ≤ ‖A - B * Q‖ :=
  frobenius_norm_sub_mul_le_of_isPolarDecomposition h.isPolarDecomposition_of_square

/-- The trace of the symmetric polar factor of `C` is the sum of the singular values of `C`: the
factor is `V diag(σ) Vᴴ` with `V` the right singular unitary (`Aᴴ A = V diag(σ²) Vᴴ`). -/
theorem IsPolarDecomposition.trace_eq_sum_colSingularValues {n : Type*} [Fintype n]
    {C U : Matrix n p 𝕜} {P : Matrix p p 𝕜} (h : IsPolarDecomposition C U P) :
    trace P = ∑ i, ((C.colSingularValues i : ℝ) : 𝕜) := by
  have hP' : (C.rightSingularUnitary * diagonal (fun i => ((C.colSingularValues i : ℝ) : 𝕜)) *
      star C.rightSingularUnitary).PosSemidef := by
    rw [star_eq_conjTranspose]
    refine PosSemidef.mul_mul_conjTranspose_same ?_ _
    exact posSemidef_diagonal_iff.2 fun i => RCLike.ofReal_nonneg.2 (colSingularValues_nonneg C i)
  have hPP : (C.rightSingularUnitary * diagonal (fun i => ((C.colSingularValues i : ℝ) : 𝕜)) *
      star C.rightSingularUnitary) * (C.rightSingularUnitary *
        diagonal (fun i => ((C.colSingularValues i : ℝ) : 𝕜)) * star C.rightSingularUnitary)
      = Cᴴ * C := by
    rw [conj_diagonal_mul_conj_diagonal, conjTranspose_mul_self_eq_conj_diagonal]
    congr 3
    funext i
    push_cast
    ring
  have hP : P = C.rightSingularUnitary * diagonal (fun i => ((C.colSingularValues i : ℝ) : 𝕜)) *
      star C.rightSingularUnitary := by
    rw [h.eq_cfcSqrt, ← hPP]
    open scoped MatrixOrder in exact CFC.sqrt_mul_self _ hP'.nonneg
  rw [hP, trace_mul_comm, ← Matrix.mul_assoc, C.star_mul_rightSingularUnitary, Matrix.one_mul,
    trace_diagonal]

/-- **The singular-value trace bound** ([golub2013matrix] §6.4.1, `tr(ZΣ) = ∑ z_ii σ_i ≤ ∑ σ_i`):
for unitary `Q`, `re tr(Q C) ≤ ∑ σ_i(C)`. With a polar decomposition `C = Q₀ P`,
`re tr(Q Q₀ P) ≤ re tr P` (`Matrix.re_trace_mul_le_trace_of_posSemidef`) and `tr P = ∑ σ_i`
(`Matrix.IsPolarDecomposition.trace_eq_sum_colSingularValues`). -/
theorem re_trace_mul_le_sum_colSingularValues (C : Matrix p p 𝕜) {Q : Matrix p p 𝕜}
    (hQ : Q ∈ unitaryGroup p 𝕜) : RCLike.re (trace (Q * C)) ≤ ∑ i, C.colSingularValues i := by
  obtain ⟨Q₀, P, h⟩ := exists_isPolarDecomposition C le_rfl
  have hW : Q * Q₀ ∈ unitaryGroup p 𝕜 := mul_mem hQ h.mem_unitaryGroup
  calc RCLike.re (trace (Q * C)) = RCLike.re (trace (Q * Q₀ * P)) := by
        rw [h.eq_mul, Matrix.mul_assoc]
    _ ≤ RCLike.re (trace P) := re_trace_mul_le_trace_of_posSemidef hW h.posSemidef
    _ = ∑ i, C.colSingularValues i := by
        rw [h.trace_eq_sum_colSingularValues, map_sum]
        simp only [RCLike.ofReal_re]

/-- **The equality case of the singular-value trace bound** ([golub2013matrix] §6.4.1, "The upper
bound is clearly attained by setting `Z = I_p`"): for an SVD `Uᴴ C V = Σ`,
`tr(V Uᴴ C) = ∑ σ_i`, and `∑ σ_i = ∑ σ_i(C)`. -/
theorem IsSVD.re_trace_mul_eq_sum {n : ℕ} {C U V : Matrix (Fin n) (Fin n) 𝕜} {σ : ℕ → ℝ}
    (h : IsSVD C U σ V) : RCLike.re (trace (V * Uᴴ * C)) = ∑ i, C.colSingularValues i := by
  have hp := h.isPolarDecomposition_of_square
  have hUU : Uᴴ * U = 1 := by
    rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.1 h.mem_unitaryGroup_left
  have hC : V * Uᴴ * C = V * diagonal (fun i : Fin n => ((σ i : ℝ) : 𝕜)) * Vᴴ := by
    conv_lhs => rw [hp.eq_mul]
    calc V * Uᴴ * (U * Vᴴ * (V * diagonal (fun i : Fin n => ((σ i : ℝ) : 𝕜)) * Vᴴ))
        = V * (Uᴴ * U) * Vᴴ * (V * diagonal (fun i : Fin n => ((σ i : ℝ) : 𝕜)) * Vᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hUU, Matrix.mul_one, ← star_eq_conjTranspose,
          mem_unitaryGroup_iff.1 h.mem_unitaryGroup_right, Matrix.one_mul]
  rw [hC, hp.trace_eq_sum_colSingularValues, map_sum]
  simp only [RCLike.ofReal_re]

end Matrix
