import Numlib.LinearAlgebra.Matrix.InverseDecay

/-!
# Cartis–Gould–Toint, Appendix B: Appendix to Chapter 10

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], Appendix B, "Appendix to
Chapter 10": Lemma B.10.1, the off-diagonal decay of the inverse of a symmetric
positive-definite tridiagonal matrix, specialized from the Demko–Moss–Smith bound
`Matrix.abs_inv_apply_le_of_isTridiagonal`. The appendix proofs of Theorems 10.2.2, 10.3.2 and
Corollaries 10.2.3, 10.3.3 are the proofs of those Chapter 10 results.

The extreme eigenvalues of a real symmetric matrix `T` are written `⨅ k, eigenvalues k` and
`⨆ k, eigenvalues k`, and `κ(T) = λ_max(T)/λ_min(T)` is the spectral condition number. Symmetry
is part of Mathlib's `Matrix.PosDef` (it includes `IsHermitian`, which for real matrices is
symmetry), so it is not a separate hypothesis. Indices run over `Fin m` (from `0`), which does
not affect `|i - j|`.
-/

namespace CartisGouldToint.AppendixB

/-- **Lemma B.10.1 (Inverse of a positive-definite tridiagonal matrix)** of
[cartis2022evaluation]. Let `T ∈ ℝ^{m×m}` be symmetric, positive definite and tridiagonal. Then
for all `i, j`,
`|(T⁻¹)ᵢⱼ| ≤ (2/λ_min(T)) ((√κ(T) - 1)/(√κ(T) + 1))^{|i-j|}`, `κ(T) = λ_max(T)/λ_min(T)`. -/
theorem lemma_B_10_1 {m : ℕ} {T : Matrix (Fin m) (Fin m) ℝ} (hT : T.PosDef)
    (htri : T.IsTridiagonal) (i j : Fin m) :
    let lmin := ⨅ k, hT.1.eigenvalues k
    let κ := (⨆ k, hT.1.eigenvalues k) / lmin
    |T⁻¹ i j| ≤ 2 / lmin * ((√κ - 1) / (√κ + 1)) ^ ((i : ℤ) - j).natAbs :=
  Matrix.abs_inv_apply_le_of_isTridiagonal hT htri i j

end CartisGouldToint.AppendixB
