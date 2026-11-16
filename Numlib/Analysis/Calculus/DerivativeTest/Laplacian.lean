/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.Laplacian`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Numlib.Analysis.Calculus.DerivativeTest

/-!
# The Laplacian at a local maximum

Let $E$ be a finite-dimensional real inner product space, and let $f : E \to \mathbb{R}$ be $C^2$ at
a local maximum $x_0$. Then $\Delta f(x_0) \le 0$. This follows from the Hessian test along an
orthonormal basis, as in [brezis2011functional], Chapter 8, Remark 27, and Theorem 10.6. It is the
pointwise input of the parabolic maximum principle (`Numlib.Analysis.PDE.Heat.Classical`) and of the
classical elliptic maximum principle.

## Main results

* `IsLocalMax.laplacian_nonpos`: $\Delta f(x_0) \le 0$ at a local maximum $x_0$ of a function that
  is $C^2$ at $x_0$.
-/

section Laplacian

open InnerProductSpace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **Laplacian is nonpositive at a local maximum**. Let $E$ be a finite-dimensional real inner
product space, and let $f : E \to \mathbb{R}$ have a local maximum at $x_0$ and be $C^2$ at
$x_0$. Then $\Delta f(x_0) \le 0$.

The Laplacian is `InnerProductSpace.laplacian`. For an orthonormal basis $(b_i)$,
$\Delta f(x_0) = \sum_i D^2 f(x_0)[b_i, b_i]$ by
`InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis`, and each term is nonpositive
by `IsLocalMax.fderiv_fderiv_apply_self_nonpos`. -/
theorem IsLocalMax.laplacian_nonpos [FiniteDimensional ℝ E] {f : E → ℝ} {x₀ : E}
    (hmax : IsLocalMax f x₀) (hf : ContDiffAt ℝ 2 f x₀) : Δ f x₀ ≤ 0 := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f (stdOrthonormalBasis ℝ E)]
  refine Finset.sum_nonpos fun i _ => ?_
  simpa only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using
    hmax.fderiv_fderiv_apply_self_nonpos hf ((stdOrthonormalBasis ℝ E) i)

end Laplacian
