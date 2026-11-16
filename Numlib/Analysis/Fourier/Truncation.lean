/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Order.Filter.AtTopBot.Interval
import Numlib.Analysis.Fourier.TrigonometricBasis
import Numlib.Analysis.Normed.Module.BestApprox

/-!
# The Fourier truncation projection on $L^2$ of the circle

Let $T > 0$ and let $L^2(\mathbb{T}_T)$ be the real $L^2$ space of the circle of circumference $T$
with its Haar probability measure. The truncation $P_n$ of a Fourier series to the frequencies of
absolute value at most $n$ is the orthogonal projection of $L^2(\mathbb{T}_T)$ onto the
trigonometric polynomials of degree at most $n$. This module defines $P_n$ as a bounded operator, so
that it can be used in the framework of projection methods. It proves that $P_n$ is idempotent, that
$\|P_n\| \le 1$, and that $P_n f \to f$ for every $f$.

The Fourier–Galerkin method for an integral equation on the circle is the projection method for the
family $(P_n)$. The two facts that a projection method needs, the uniform boundedness of the
projections and their pointwise convergence, are the last two results below. The $L^2$ convergence
of Fourier series is Example 1.3.15 of [han2009theoretical], and the projection method that uses
these facts is in §12.2.4 and §13.3.1 of [han2009theoretical].

## Main definitions

* `trigPolyLp`: the subspace of $L^2(\mathbb{T}_T)$ spanned by the members $t_m$ of the real
  trigonometric system with $|m| \le n$. It is the image in $L^2$ of the space `trigPolyLE T n` of
  continuous trigonometric polynomials.
* `trigProjCLM`: the orthogonal projection $P_n$ onto this subspace, the Fourier truncation.

## Main results

* `isIdempotentElem_trigProjCLM`: $P_n^2 = P_n$.
* `norm_trigProjCLM_le_one`: $\|P_n\| \le 1$, so the family $(P_n)$ is uniformly bounded. There is
  no Lebesgue constant, unlike for the truncation on the continuous functions, whose norm grows like
  $\log n$.
* `tendsto_norm_sub_trigPartialSum`: the $L^2$ error of the Fourier partial sum tends to $0$.
* `tendsto_trigProjCLM`: $P_n f \to f$ in $L^2$ for every $f$, which is Parseval's identity read
  along the symmetric blocks of frequencies.
-/

open AddCircle Filter MeasureTheory Submodule Topology

open scoped Real

variable {T : ℝ} [hT : Fact (0 < T)] {n : ℕ}

/-- The **trigonometric polynomials of degree at most $n$ in $L^2$**: for $T > 0$ and
$n \in \mathbb{N}$, the subspace of $L^2(\mathbb{T}_T)$ spanned by the members $t_m$ of the real
trigonometric system with $|m| \le n$.

It is the $L^2$ counterpart of `trigPolyLE`, and it has dimension $2n + 1$. -/
noncomputable def trigPolyLp (T : ℝ) [hT : Fact (0 < T)] (n : ℕ) :
    Submodule ℝ (Lp ℝ 2 (@haarAddCircle T hT)) :=
  span ℝ (trigLp T '' Set.Icc (-(n : ℤ)) n)

instance : FiniteDimensional ℝ (trigPolyLp T n) :=
  FiniteDimensional.span_of_finite ℝ ((Set.finite_Icc _ _).image _)

instance : (trigPolyLp T n).HasOrthogonalProjection :=
  HasOrthogonalProjection.ofCompleteSpace _

/-- For $m \in \mathbb{Z}$ with $-n \le m \le n$, the member $t_m$ of the real trigonometric system
lies in the subspace `trigPolyLp T n`. -/
theorem trigLp_mem_trigPolyLp {m : ℤ} (hm : m ∈ Finset.Icc (-(n : ℤ)) n) :
    trigLp T m ∈ trigPolyLp T n :=
  subset_span ⟨m, Set.mem_Icc.2 (Finset.mem_Icc.1 hm), rfl⟩

/-- For $f \in L^2(\mathbb{T}_T)$ and $n \in \mathbb{N}$, the Fourier partial sum
$S_n f = \sum_{|m| \le n} r_m(f) \, t_m$ lies in the subspace of trigonometric polynomials of
degree at most $n$. -/
theorem trigPartialSum_mem_trigPolyLp (n : ℕ) (f : Lp ℝ 2 (@haarAddCircle T hT)) :
    trigPartialSum n f ∈ trigPolyLp T n :=
  sum_mem fun _ hm => Submodule.smul_mem _ _ (trigLp_mem_trigPolyLp hm)

/-- The **Fourier truncation** $P_n$ on $L^2(\mathbb{T}_T)$, for $T > 0$ and $n \in \mathbb{N}$: the
orthogonal projection onto the subspace of trigonometric polynomials of degree at most $n$, as a
bounded linear operator.

The operator agrees with the partial sum $S_n$ (`trigPartialSum n`), and this makes it
computable from the Fourier coefficients. The results below use only that $P_n$ is an orthogonal
projection onto a subspace that contains $S_n f$. -/
noncomputable def trigProjCLM (T : ℝ) [hT : Fact (0 < T)] (n : ℕ) :
    Lp ℝ 2 (@haarAddCircle T hT) →L[ℝ] Lp ℝ 2 (@haarAddCircle T hT) :=
  (trigPolyLp T n).starProjection

/-- The Fourier truncation is a projection: $P_n^2 = P_n$ for every $T > 0$ and $n \in \mathbb{N}$.
-/
theorem isIdempotentElem_trigProjCLM (T : ℝ) [hT : Fact (0 < T)] (n : ℕ) :
    IsIdempotentElem (trigProjCLM T n) :=
  isIdempotentElem_starProjection _

/-- **The Fourier truncation has norm at most one on $L^2$**: for every $T > 0$ and
$n \in \mathbb{N}$, $\|P_n\| \le 1$.

The operator $P_n$ is an orthogonal projection, so the family $(P_n)$ is uniformly bounded. In
contrast, the same truncation on the continuous periodic functions has as its norm the Lebesgue
constant, which grows like $\log n$. -/
theorem norm_trigProjCLM_le_one (T : ℝ) [hT : Fact (0 < T)] (n : ℕ) : ‖trigProjCLM T n‖ ≤ 1 :=
  starProjection_norm_le _

/-- For $f \in L^2(\mathbb{T}_T)$, the $L^2$ error of the Fourier partial sum tends to zero:
$$\|f - S_n f\| \to 0 \quad \text{as } n \to \infty.$$
This is Parseval's identity read along the symmetric blocks of frequencies $|m| \le n$. -/
theorem tendsto_norm_sub_trigPartialSum (f : Lp ℝ 2 (@haarAddCircle T hT)) :
    Tendsto (fun n => ‖f - trigPartialSum n f‖) atTop (𝓝 0) := by
  have hpart : Tendsto (fun n : ℕ => ∑ m ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
      realFourierCoeff (f : AddCircle T → ℝ) m ^ 2) atTop (𝓝 (‖f‖ ^ 2)) :=
    (hasSum_sq_realFourierCoeff f).comp (Finset.tendsto_Icc_neg (R := ℤ))
  have hsq : Tendsto (fun n => ‖f - trigPartialSum n f‖ ^ 2) atTop (𝓝 0) := by
    have := tendsto_const_nhds (x := ‖f‖ ^ 2) (f := atTop (α := ℕ)) |>.sub hpart
    rw [sub_self] at this
    exact this.congr fun n => (norm_sub_trigPartialSum_sq n f).symm
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using
    (Real.continuous_sqrt.tendsto 0).comp hsq

/-- **The Fourier truncations converge pointwise to the identity on $L^2$**: for every
$f \in L^2(\mathbb{T}_T)$,
$$P_n f \to f \quad \text{in } L^2 \text{ as } n \to \infty.$$
Together with `norm_trigProjCLM_le_one`, this is everything that a projection method needs from
the family $(P_n)$.

The orthogonal projection is at least as good an approximation as the partial sum $S_n f$, which
lies in the same subspace. So $\|f - P_n f\| \le \|f - S_n f\|$, and the bound tends to $0$ by
`tendsto_norm_sub_trigPartialSum`. -/
theorem tendsto_trigProjCLM (f : Lp ℝ 2 (@haarAddCircle T hT)) :
    Tendsto (fun n => trigProjCLM T n f) atTop (𝓝 f) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (tendsto_norm_sub_trigPartialSum f)
  rw [norm_sub_rev]
  exact (isBestApprox_starProjection (trigPolyLp T n) f).2 _
    (trigPartialSum_mem_trigPolyLp n f)
