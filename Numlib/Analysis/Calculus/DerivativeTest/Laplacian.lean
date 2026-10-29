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

`IsLocalMax.laplacian_nonpos`: on a finite-dimensional real inner product space, `Δ f x₀ ≤ 0` at a
local maximum of a `C²` function, the Hessian test `IsLocalMax.fderiv_fderiv_apply_self_nonpos`
along an orthonormal basis. It is the pointwise input of the parabolic maximum principle
(`Numlib.Analysis.PDE.Heat.Classical`) and of the classical elliptic one.

## References

[brezis2011functional], chapter 8, Remark 27, and Theorem 10.6.
-/

section Laplacian

open InnerProductSpace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The Laplacian is nonpositive at a local maximum** of a `C²` function on a
finite-dimensional real inner product space: by `laplacian_eq_iteratedFDeriv_orthonormalBasis`,
`Δ f x₀ = ∑ᵢ D²f (x₀) [bᵢ, bᵢ]`, and each term is nonpositive
(`IsLocalMax.fderiv_fderiv_apply_self_nonpos`). -/
theorem IsLocalMax.laplacian_nonpos [FiniteDimensional ℝ E] {f : E → ℝ} {x₀ : E}
    (hmax : IsLocalMax f x₀) (hf : ContDiffAt ℝ 2 f x₀) : Δ f x₀ ≤ 0 := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f (stdOrthonormalBasis ℝ E)]
  refine Finset.sum_nonpos fun i _ => ?_
  simpa only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using
    hmax.fderiv_fderiv_apply_self_nonpos hf ((stdOrthonormalBasis ℝ E) i)

end Laplacian
