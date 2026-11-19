/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.Convergence.CGActiveSpectrum

/-!
# Liesen and Strakoš, §5.6.2: Active eigenvalues for CG

The spectral minimax value before the last possible CG step is determined
by a subset of distinct eigenvalues and has a Lagrange interpolation formula.

## Deviations from the source

* **Equation (5.6.20)** (index correction). The left-hand maximum in the
  printed equation ranges from $1$ to $N$ but uses the hatted eigenvalue
  notation. Here that maximum ranges over the full spectrum, as in
  (5.6.19), and the $n+1$ selected eigenvalues index the product formula.
-/

open Finset Polynomial

namespace LiesenStrakos.Chapter05

/-- **Theorem 5.6.6** of [liesen2013krylov], active-eigenvalue formula (5.6.20).
Let $A$ be symmetric coercive and let $0<n<d_{\min}(A)$. Then $n+1$ distinct
eigenvalues suffice to determine the degree-$n$ minimax bound, whose value
is the reciprocal of the sum of the absolute Lagrange basis values at zero.

**Correction.** Corrects full-spectrum maximum and uses selected eigenvalues on the certificate
side.
-/
theorem theorem_5_6_6_certificate
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {A : E →ₗ[𝕜] E} {N : ℕ} (hN : Module.finrank 𝕜 E = N)
    (hA : A.IsSymmetricCoercive) {n : ℕ} (hn : 0 < n) (hd : n < (minpoly 𝕜 A).natDegree) :
    ∃ T ⊆ Finset.univ.image (hA.isSymmetric.eigenvalues hN), T.card = n + 1 ∧
      (⨅ p : {p : 𝕜[X] // p.degree ≤ n ∧ p.eval 0 = 1},
        ⨆ i, ‖p.1.eval (hA.isSymmetric.eigenvalues hN i : 𝕜)‖) =
        (∑ x ∈ T, ∏ y ∈ T.erase x, |y| / |y - x|)⁻¹ :=
  CG.exists_activeEigenvalues hN hA.isSymmetric hn hd

end LiesenStrakos.Chapter05
