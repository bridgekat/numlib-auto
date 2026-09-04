import Numlib.InnerProductSpace.Energy
import Numlib.InnerProductSpace.Compression
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Algebra.Polynomial.Module.AEval

/-!
# Polynomials in a symmetric operator: spectral norm bounds

`‖p(A) x‖ ≤ max_{λ ∈ σ(A)} |p(λ)| ‖x‖` and the energy-norm analogue for symmetric `A` in finite
dimension (via `LinearMap.IsSymmetric.eigenvectorBasis`), and the real-interval form used by the
Chebyshev bounds: for `A.IsSymmetricBoundedBy a b`, `‖p(A) x‖ ≤ sup_{[a,b]} |p| ‖x‖` in *any*
inner product space, obtained by compressing `A` to the finite-dimensional
`span {x, A x, …, A^(deg p) x}` (the "compression trick"; Saad Lemma 6.28/6.31 proofs, Saad-eig
Lemma 6.1, AH (5.6.16)–(5.6.19), Meurant (3.7)–(3.8)). The Hilbert-space version via the
continuous functional calculus is a phase-2 alternative, not needed for the statements.
-/

open Polynomial

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

section FiniteDimensional

variable [FiniteDimensional 𝕜 E]

namespace LinearMap.IsSymmetric

variable {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
include hA

/-- Eigenvalues of `p(A)` are `p(λ)`; hence `‖p(A) x‖ ≤ C ‖x‖` whenever `‖p(λ)‖ ≤ C` on the
spectrum. -/
theorem norm_aeval_apply_le {C : ℝ} (p : 𝕜[X])
    (hC : ∀ μ : 𝕜, Module.End.HasEigenvalue A μ → ‖p.eval μ‖ ≤ C) (x : E) :
    ‖aeval A p x‖ ≤ C * ‖x‖ := by
  sorry

/-- Energy-norm version for symmetric coercive `A`. -/
theorem energyNorm_aeval_apply_le (hA' : A.IsSymmetricCoercive) {C : ℝ} (p : 𝕜[X])
    (hC : ∀ μ : 𝕜, Module.End.HasEigenvalue A μ → ‖p.eval μ‖ ≤ C) (x : E) :
    energyNorm A (aeval A p x) ≤ C * energyNorm A x := by
  sorry

/-- The eigenvalues of a symmetric operator are real. -/
theorem im_eq_zero_of_hasEigenvalue {μ : 𝕜} (hμ : Module.End.HasEigenvalue A μ) :
    RCLike.im μ = 0 := by
  sorry

end LinearMap.IsSymmetric

/-- Saad Prop 6.32 (diagonalizable `A`): if `A` is conjugate by `X` to an operator `D` whose
polynomial images satisfy `‖p(D) y‖ ≤ C ‖y‖`, then `‖p(A) x‖ ≤ κ(X) C ‖x‖`. Stated with `D`
symmetric so that the finite-dimensional bound above applies. -/
theorem norm_aeval_apply_le_of_conj {A D : E →ₗ[𝕜] E} (X : E ≃L[𝕜] E)
    (hconj : A = (X : E →ₗ[𝕜] E) ∘ₗ D ∘ₗ (X.symm : E →ₗ[𝕜] E)) (hD : D.IsSymmetric) {C : ℝ}
    (p : 𝕜[X]) (hC : ∀ μ : 𝕜, Module.End.HasEigenvalue D μ → ‖p.eval μ‖ ≤ C) (x : E) :
    ‖aeval A p x‖ ≤ ‖(X : E →L[𝕜] E)‖ * ‖(X.symm : E →L[𝕜] E)‖ * C * ‖x‖ := by
  sorry

end FiniteDimensional

section Compression

/-! ### The compression trick

Everything a Krylov method does in `m` steps happens inside the finite-dimensional
`𝒦_{m+1}`, on which `A` acts (up to the last step) as its compression. -/

namespace compression

variable (A : E →ₗ[𝕜] E) (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]

/-- Quadratic-form bounds pass to compressions. -/
theorem isSymmetricBoundedBy {lmin lmax : ℝ} (hA : A.IsSymmetricBoundedBy lmin lmax) :
    (compression A K).IsSymmetricBoundedBy lmin lmax := by
  sorry

theorem isSymmetricCoercive (hA : A.IsSymmetricCoercive) :
    (compression A K).IsSymmetricCoercive := by
  sorry

theorem energyInner_apply (x y : K) : energyInner (compression A K) x y = energyInner A x y := by
  sorry

theorem energyNorm_apply (x : K) : energyNorm (compression A K) x = energyNorm A x := by
  sorry

end compression

end Compression

namespace LinearMap.IsSymmetricBoundedBy

variable {A : E →ₗ[𝕜] E} {a b : ℝ} (hA : A.IsSymmetricBoundedBy a b)
include hA

/-- Real-interval form, in any inner product space: `‖p(A) x‖ ≤ sup_{[a,b]} |p| ‖x‖` for a real
polynomial `p`. -/
theorem norm_aeval_map_apply_le (p : ℝ[X]) (x : E) :
    ‖aeval A (p.map (algebraMap ℝ 𝕜)) x‖ ≤
      sSup ((fun t => |p.eval t|) '' Set.Icc a b) * ‖x‖ := by
  sorry

/-- Energy-norm version (`0 < a`). -/
theorem energyNorm_aeval_map_apply_le (ha : 0 < a) (p : ℝ[X]) (x : E) :
    energyNorm A (aeval A (p.map (algebraMap ℝ 𝕜)) x) ≤
      sSup ((fun t => |p.eval t|) '' Set.Icc a b) * energyNorm A x := by
  sorry

end LinearMap.IsSymmetricBoundedBy
