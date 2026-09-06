import Numlib.Krylov.Convergence.Polynomial
import Numlib.Krylov.Iterate
import Numlib.RingTheory.Polynomial.ChebyshevMinimax

/-!
# Chebyshev convergence bound for MINRES on an indefinite system

The single-interval Chebyshev argument of `Numlib/Krylov/Convergence/CG.lean` needs a spectrum
bounded away from the origin on one side of it, so it says nothing about a symmetric *indefinite*
system.  The classical replacement encloses the spectrum in two intervals `[a₁, b₁] ∪ [a₂, b₂]` with
`a₁ < b₁ < 0 < a₂ < b₂` of equal length, and composes the Chebyshev polynomial of one interval with
the quadratic that folds the two onto it; that is
`Polynomial.Chebyshev.exists_eval_zero_eq_one_abs_le_of_union_Icc` of
`Numlib/RingTheory/Polynomial/ChebyshevMinimax.lean`, and the only work left here is to feed it to
the optimality of a minimal-residual iterate.  The resulting bound
(`Krylov.IsMinResIterate.norm_residual_le_of_eigenvalues_mem_union_Icc`) is on the *even* steps,
because the competitor polynomial has degree `2k`, and its rate is governed by the two products of
endpoints across the origin: the outer one `|a₁ b₂|` and the inner one `|b₁ a₂|`.

This is [greenbaum1997iterative] Thm 3.1.1, the estimate [choi2006iterative] §2.4 and [fong2012cg]
§1 quote for MINRES.

## Implementation notes

The hypothesis is a two-interval enclosure of the spectrum, not a quadratic-form bound, so the
compression trick of `Numlib/Krylov/Convergence/Polynomial.lean` — which transports a
`LinearMap.IsSymmetricBoundedBy` hypothesis to the compression of `A` to a Krylov subspace — does
not apply: an eigenvalue of a compression need not be an eigenvalue of `A`, and the two intervals
say nothing about the values of the quadratic form between them.  The statement is therefore at the
finite-dimensional rung, where `LinearMap.IsSymmetric.norm_aeval_apply_le` reads the norm of `p(A)`
off the eigenvalues directly.  A Hilbert-space version would go through the continuous functional
calculus.
-/

open Polynomial Polynomial.Chebyshev

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Krylov

/-- **The Chebyshev bound for MINRES on a symmetric indefinite system**
([greenbaum1997iterative], Thm 3.1.1; [choi2006iterative], §2.4).  If every eigenvalue of the
symmetric `A` lies in `[a₁, b₁] ∪ [a₂, b₂]` with `a₁ < b₁ < 0 < a₂ < b₂` and the two intervals of
equal length, then a minimal-residual iterate over `𝒦_{2k}` satisfies

`‖b - A x‖ ≤ 2 ((√|a₁ b₂| - √|b₁ a₂|) / (√|a₁ b₂| + √|b₁ a₂|))^k ‖b - A x₀‖`.

Only the even steps are bounded: the competitor polynomial is a degree-`k` Chebyshev polynomial
composed with a quadratic, hence of degree `2k`, and the residual norms are nonincreasing
(`Krylov.IsMinResIterate.norm_residual_antitone`) so nothing is lost. -/
theorem IsMinResIterate.norm_residual_le_of_eigenvalues_mem_union_Icc [FiniteDimensional 𝕜 E]
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {a₁ b₁ a₂ b₂ : ℝ} (h₁ : a₁ < b₁) (hb₁ : b₁ < 0)
    (ha₂ : 0 < a₂) (h₂ : a₂ < b₂) (hlen : b₁ - a₁ = b₂ - a₂)
    (hspec : ∀ μ : 𝕜, Module.End.HasEigenvalue A μ →
      RCLike.re μ ∈ Set.Icc a₁ b₁ ∪ Set.Icc a₂ b₂)
    {b x₀ x : E} {k : ℕ} (hx : IsMinResIterate A b x₀ (2 * k) x) :
    ‖b - A x‖ ≤
      2 * ((Real.sqrt |a₁ * b₂| - Real.sqrt |b₁ * a₂|) /
        (Real.sqrt |a₁ * b₂| + Real.sqrt |b₁ * a₂|)) ^ k * ‖b - A x₀‖ := by
  obtain ⟨p, hdeg, hp0, hple⟩ :=
    exists_eval_zero_eq_one_abs_le_of_union_Icc h₁ hb₁ ha₂ h₂ hlen k
  set q : 𝕜[X] := p.map (algebraMap ℝ 𝕜) with hq
  have hqdeg : q.degree ≤ (2 * k : ℕ) := degree_map_le.trans hdeg
  have hq0 : q.eval 0 = 1 := by rw [hq, eval_zero_map, hp0, map_one]
  have hbound : ∀ μ : 𝕜, Module.End.HasEigenvalue A μ →
      ‖q.eval μ‖ ≤ 2 * ((Real.sqrt |a₁ * b₂| - Real.sqrt |b₁ * a₂|) /
        (Real.sqrt |a₁ * b₂| + Real.sqrt |b₁ * a₂|)) ^ k := by
    intro μ hμ
    have hre : ((RCLike.re μ : ℝ) : 𝕜) = μ :=
      RCLike.conj_eq_iff_re.mp
        (RCLike.conj_eq_iff_im.mpr (hA.im_eq_zero_of_hasEigenvalue hμ))
    have heval : q.eval μ = ((p.eval (RCLike.re μ) : ℝ) : 𝕜) := by
      conv_lhs => rw [← hre]
      rw [hq, eval_map, ← RCLike.algebraMap_eq_ofReal, eval₂_at_apply,
        RCLike.algebraMap_eq_ofReal]
    rw [heval, RCLike.norm_ofReal]
    exact hple _ (hspec μ hμ)
  calc ‖b - A x‖ ≤ ‖aeval A q (b - A x₀)‖ := hx.norm_residual_le_norm_aeval q hqdeg hq0
    _ ≤ _ := hA.norm_aeval_apply_le q hbound _

end Krylov
