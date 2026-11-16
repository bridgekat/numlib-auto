/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.Convergence.Polynomial
import Numlib.Krylov.Iterate
import Numlib.RingTheory.Polynomial.ChebyshevMinimax

/-!
# Chebyshev convergence bound for MINRES on an indefinite system

Let $A$ be a symmetric operator on a finite-dimensional inner product space, and let $x_m$ be a
minimal-residual iterate for $Ax = b$ from $x_0$: $x_m - x_0$ lies in the Krylov subspace
$\mathcal{K}_m(A, r_0)$ with $r_0 = b - A x_0$, and $\|b - A x_m\|$ is minimal over
$x_0 + \mathcal{K}_m(A, r_0)$. The single-interval Chebyshev bound of `Numlib.Krylov.Convergence.CG`
needs a spectrum on one side of the origin, so it says nothing about a symmetric *indefinite*
system. The classical replacement encloses the spectrum in two intervals
$[a_1, b_1] \cup [a_2, b_2]$ of equal length with $a_1 < b_1 < 0 < a_2 < b_2$. The competitor
polynomial is the Chebyshev polynomial of one interval composed with a quadratic that folds the two
intervals onto it (`Polynomial.Chebyshev.exists_eval_zero_eq_one_abs_le_of_union_Icc`), and this
module combines it with the optimality of a minimal-residual iterate.

The resulting bound is on the even steps, because the competitor polynomial has degree $2k$. Its
rate depends on two products of endpoints across the origin: the outer one $|a_1 b_2|$ and the inner
one $|b_1 a_2|$. This is Theorem 3.1.1 of [greenbaum1997iterative], the estimate that
[choi2006iterative], §2.4, and [fong2012cg], §1, quote for MINRES.

## Main results

* `Krylov.IsMinResidualIterate.norm_residual_le_of_eigenvalues_mem_union_Icc`: if the eigenvalues of
  $A$ lie in $[a_1, b_1] \cup [a_2, b_2]$, then the residual of a minimal-residual iterate at step
  $2k$ is at most $2 \rho^k$ times the initial residual, where $\rho = (\sqrt{|a_1 b_2|} -
  \sqrt{|b_1 a_2|}) / (\sqrt{|a_1 b_2|} + \sqrt{|b_1 a_2|})$.

## Implementation notes

* The hypothesis is a two-interval enclosure of the spectrum, not a bound on the quadratic form.
  Therefore the compression argument of `Numlib.Krylov.Convergence.Polynomial`, which transports a
  `LinearMap.IsSymmetricBoundedBy` hypothesis to the compression of $A$ to a Krylov subspace, does
  not apply: an eigenvalue of a compression need not be an eigenvalue of $A$, and the two intervals
  say nothing about the values of the quadratic form between them.
* For this reason the statement is in finite dimension, where
  `LinearMap.IsSymmetric.norm_aeval_apply_le` bounds the norm of $p(A)$ by the values of $p$ at the
  eigenvalues of $A$. A version for Hilbert spaces would go through the continuous functional
  calculus.
-/

open Polynomial Polynomial.Chebyshev

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Krylov

/-- The **Chebyshev bound for MINRES on a symmetric indefinite system**. Let $E$ be a
finite-dimensional inner product space over $\mathbb{R}$ or $\mathbb{C}$, and let $A : E \to E$
be symmetric. Let $a_1 < b_1 < 0 < a_2 < b_2$ with $b_1 - a_1 = b_2 - a_2$, and suppose that
every eigenvalue of $A$ (which is real) lies in $[a_1, b_1] \cup [a_2, b_2]$. If $x$ is a
minimal-residual iterate for $Ax = b$ from $x_0$ over $\mathcal{K}_{2k}(A, b - A x_0)$, then
$$\|b - Ax\| \le 2 \left( \frac{\sqrt{|a_1 b_2|} - \sqrt{|b_1 a_2|}}{\sqrt{|a_1 b_2|} +
  \sqrt{|b_1 a_2|}} \right)^k \|b - A x_0\|.$$
This is Theorem 3.1.1 of [greenbaum1997iterative], quoted for MINRES in [choi2006iterative],
§2.4.

Only the even steps are bounded, because the competitor polynomial is a Chebyshev polynomial of
degree $k$ composed with a quadratic, so it has degree $2k$. Nothing is lost, since the residual
norms of minimal-residual iterates are nonincreasing
(`Krylov.IsMinResidualIterate.norm_residual_antitone`). The Lean hypothesis on the eigenvalues
is stated for the real part `RCLike.re μ` of each eigenvalue $\mu$. -/
theorem IsMinResidualIterate.norm_residual_le_of_eigenvalues_mem_union_Icc [FiniteDimensional 𝕜 E]
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {a₁ b₁ a₂ b₂ : ℝ} (h₁ : a₁ < b₁) (hb₁ : b₁ < 0)
    (ha₂ : 0 < a₂) (h₂ : a₂ < b₂) (hlen : b₁ - a₁ = b₂ - a₂)
    (hspec : ∀ μ : 𝕜, Module.End.HasEigenvalue A μ →
      RCLike.re μ ∈ Set.Icc a₁ b₁ ∪ Set.Icc a₂ b₂)
    {b x₀ x : E} {k : ℕ} (hx : IsMinResidualIterate A b x₀ (2 * k) x) :
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
