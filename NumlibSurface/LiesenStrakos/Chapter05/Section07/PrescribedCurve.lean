/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.Convergence.GMRESCurve

/-!
# Liesen and Strakoš, §5.7.4: Prescribed GMRES convergence curves

Theorem 5.7.7 gives a linear system whose GMRES residual norms and spectrum
are prescribed independently.
-/

open Krylov Polynomial

namespace LiesenStrakos.Chapter05

/-- **Theorem 5.7.7** of [liesen2013krylov]. For any $N$ positive numbers
$f_0\geq\dots\geq f_{N-1}>0$ and $N$ nonzero complex numbers $\lambda_i$, there
are an $N\times N$ matrix $A$ with eigenvalues $\lambda_i$ counted with
multiplicity and a right-hand side $b$ with $\|b\|=f_0$ such that GMRES starting
at zero has residual norm $f_k$ at each step $0\le k<N$. The dimension $N$
is represented by $n+1$. -/
theorem theorem_5_7_7 (n : ℕ) (f : Fin (n + 1) → ℝ)
    (hf : Antitone f) (hpos : 0 < f (Fin.last n))
    (μ : Fin (n + 1) → ℂ) (hμ : ∀ i, μ i ≠ 0) :
    ∃ (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
      (b : EuclideanSpace ℂ (Fin (n + 1)))
      (x : ℕ → EuclideanSpace ℂ (Fin (n + 1))),
      A.charpoly = (∏ i, (X - C (μ i))) ∧ ‖b‖ = f 0 ∧
      (∀ k, IsMinResidualIterate (Matrix.toEuclideanLin A) b 0 k (x k)) ∧
      ∀ k : Fin (n + 1), ‖b - Matrix.toEuclideanLin A (x k.val)‖ = f k := by
  obtain ⟨T, b, x, hchar, _, hb, hx, hr⟩ :=
    exists_gmres_curve_and_charpoly n f hf hpos μ hμ
  let w := (EuclideanSpace.basisFun (Fin (n + 1)) ℂ).toBasis
  let A := LinearMap.toMatrix w w T
  have hA : Matrix.toEuclideanLin A = T := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.toLin_toMatrix]
  refine ⟨A, b, x, (LinearMap.charpoly_toMatrix T w).trans hchar, hb, ?_⟩
  rw [hA]
  exact ⟨hx, hr⟩

end LiesenStrakos.Chapter05
