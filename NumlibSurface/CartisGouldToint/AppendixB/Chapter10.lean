/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.InverseDecay

/-!
# Cartis, Gould and Toint, Appendix B: Appendix to Chapter 10

This module formalizes the part of Appendix B of [cartis2022evaluation] that belongs to Chapter 10:
Lemma B.10.1, the decay away from the diagonal of the entries of the inverse of a symmetric
positive-definite tridiagonal matrix $T$. With the spectral condition number $\kappa(T) =
\lambda_{\max}(T)/\lambda_{\min}(T)$, the entries satisfy $|(T^{-1})_{ij}| \le (2/\lambda_{\min}(T))
q^{|i-j|}$ with $q = (\sqrt{\kappa(T)} - 1)/(\sqrt{\kappa(T)} + 1)$. The proof specializes the bound
of Demko, Moss and Smith, `Matrix.abs_inv_apply_le_of_isTridiagonal`. The proofs of Theorems 10.2.2
and 10.3.2 and of Corollaries 10.2.3 and 10.3.3 that the book gives in this appendix are the proofs
of those results in Chapter 10.

## Main results

* Lemma B.10.1, `CartisGouldToint.AppendixB.lemma_B_10_1`: the bound on the entries of $T^{-1}$.

## Conventions

* The extreme eigenvalues $\lambda_{\min}(T)$ and $\lambda_{\max}(T)$ of a real symmetric matrix are
  the infimum and the supremum of its eigenvalues `Matrix.IsHermitian.eigenvalues`.
* Indices run over `Fin m`, from $0$; this does not change $|i - j|$.

## Implementation notes

* Symmetry is part of `Matrix.PosDef` of Mathlib, which includes `Matrix.IsHermitian`; for real
  matrices this is symmetry. So symmetry is not a separate hypothesis.
-/

namespace CartisGouldToint.AppendixB

/-- **Lemma B.10.1** of [cartis2022evaluation] (inverse of a positive-definite tridiagonal matrix).
Let $T \in \mathbb{R}^{m \times m}$ be symmetric, positive definite and tridiagonal, and let
$\kappa(T) = \lambda_{\max}(T)/\lambda_{\min}(T)$. Then for all indices $i, j$,
$$|(T^{-1})_{ij}| \le \frac{2}{\lambda_{\min}(T)} \left(\frac{\sqrt{\kappa(T)} -
  1}{\sqrt{\kappa(T)} + 1}\right)^{|i-j|}.$$

The eigenvalues $\lambda_{\min}(T)$ and $\lambda_{\max}(T)$ are the infimum and the supremum of
the eigenvalues of $T$. The hypothesis `T.PosDef` contains the symmetry of $T$. -/
theorem lemma_B_10_1 {m : ℕ} {T : Matrix (Fin m) (Fin m) ℝ} (hT : T.PosDef)
    (htri : T.IsTridiagonal) (i j : Fin m) :
    let lmin := ⨅ k, hT.1.eigenvalues k
    let κ := (⨆ k, hT.1.eigenvalues k) / lmin
    |T⁻¹ i j| ≤ 2 / lmin * ((√κ - 1) / (√κ + 1)) ^ ((i : ℤ) - j).natAbs :=
  Matrix.abs_inv_apply_le_of_isTridiagonal hT htri i j

end CartisGouldToint.AppendixB
