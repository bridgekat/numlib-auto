import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Numlib.Analysis.Fourier.LogSingleLayer
import Numlib.Approximation.CompositeQuadrature
import Mathlib.Topology.Instances.AddCircle.Real
import NumlibSurface.AtkinsonHan.Chapter12.Section04

/-!
# Atkinson–Han §13.2: the Nyström method for the boundary integral equation

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §13.2.

The interior Dirichlet problem for Laplace's equation on a planar region with smooth boundary `S`
is reformulated as the boundary integral equation of the second kind

`-π ρ(P) + ∫_S ρ(Q) ∂/∂n_Q log |P - Q| dS_Q = f(P)`,

and after a regular `C²` parametrization of `S` by arclength this is an ordinary integral equation
`(-π + K) ρ = f` on the space `C_p(L)` of continuous `L`-periodic functions, with a *continuous*
kernel: the parametrized double-layer kernel extends continuously to the diagonal, where its value
is half the curvature.  The book's own words are that "the natural function space setting for
studying (13.2.3) is `C_p(L)` with the uniform norm", and that "from this work, `(-π + K)⁻¹` exists
as a bounded operator from `C_p(L)` to `C_p(L)`" — quoted from the literature, not proved.  The
invertibility is therefore a hypothesis here, exactly as it is in the book.

`C_p(L)` is `C(AddCircle L, ℝ)`, and the boundary integral `∫_0^L … ds` is integration against the
Haar measure of `AddCircle L`, so §13.2's error analysis is Theorem 12.4.4 read at `λ = -π` on that
space.  No Sobolev space occurs anywhere in it; that is needed only for §13.2.2, the exterior
Neumann problem, and for §13.3.

## Main results

* `equation_13_2_6` — the Nyström interpolation formula, which extends the discrete solution off
  the quadrature nodes.
* `equation_13_2_7` — unique solvability of the approximating equations for all large `n`,
  uniformly bounded inverses, and `‖ρ - ρ_n‖_∞ ≤ c ‖K ρ - K_n ρ‖_∞`.
* `equation_13_2_4` — the same with the concrete periodic trapezoidal rule
  `h ∑_{j < n} k (t, j h) ρ (j h)`, `h = L / n`, whose two quadrature hypotheses are discharged by
  `Quadrature.sum_abs_circleTrapezoid` and `Quadrature.tendsto_circleTrapezoid`.
* `equation_13_2_32` — the Fourier diagonalization of the logarithmic single layer operator of
  §13.2.3, `A ψ_m = ψ_m / max {1, |m|}`, and `exercise_13_3_1`, the first kind equation it solves.

## Not formalized here

* The identification of `K` with the boundary integral `∫_S ρ(Q) ∂/∂n_Q log |P - Q| dS_Q`, which
  needs a surface measure and a normal field on `S`; only the parametrized kernel is reachable, and
  that is `Chapter13/Section01`.
* The *rate* of the trapezoidal rule — spectral convergence for a smooth periodic integrand —
  which is Proposition 7.5.6 and needs the periodic Sobolev scale `H^s(2π)`; only the bound is
  stated.  Its *convergence* for every continuous periodic integrand is no longer a hypothesis:
  `Quadrature.tendsto_circleTrapezoid` of `Numlib/Approximation/CompositeQuadrature` proves it, and
  `equation_13_2_4` is the resulting concrete scheme.
* Exercise 13.2.5, that `‖K‖ = π` for a convex region, and (13.2.14)–(13.2.23), the evaluation of
  the potential near the boundary.  Both are planar potential theory rather than numerical
  analysis: the row integral `∫_0^L k (t, s) ds` of the double layer kernel is the total turning of
  the chord direction seen from a boundary point, so it is a degree-theoretic statement about plane
  curves — an Umlaufsatz — and Mathlib has no turning number; and (13.2.16) is the maximum
  principle for harmonic functions on the region together with the jump relation (13.2.17).  See
  `plans/NumlibSurface/AtkinsonHan/Chapter13/Section02.toml`.
* The bound (13.2.33), `‖A‖_{C_p → C_p} ≤ √(1 + π²/3)`, which the book quotes from Atkinson;
  only the diagonalization (13.2.32) is proved.
-/

open Filter MeasureTheory Topology

open scoped Real

namespace AtkinsonHan.Chapter13

open IntegralOperator

variable {L : ℝ} [Fact (0 < L)]

/-- **(13.2.6), the Nyström interpolation formula.**  A solution of the discrete equations
`(-π + K_n) ρ_n = f` is determined at *every* point of the boundary by its values at the quadrature
nodes,

`ρ_n(t) = (∑_j w_j k (t, x_j) ρ_n (x_j) - f(t)) / π`,

which is the equation itself solved for `ρ_n(t)`.  This is what makes the Nyström method produce a
function rather than a table of values. -/
theorem equation_13_2_6 {m : ℕ} (w : Fin m → ℝ) (x : Fin m → AddCircle L)
    (k : C(AddCircle L × AddCircle L, ℝ)) (f ρn : C(AddCircle L, ℝ))
    (h : ((-π) • 1 + nystromCLM w x k : C(AddCircle L, ℝ) →L[ℝ] C(AddCircle L, ℝ)) ρn = f)
    (t : AddCircle L) :
    ρn t = (∑ j, w j * k (t, x j) * ρn (x j) - f t) / π := by
  have ht := congrArg (fun g : C(AddCircle L, ℝ) => g t) h
  simp only [add_apply, ContinuousMap.add_apply, smul_apply,
    ContinuousMap.smul_apply, one_apply_eq_self, smul_eq_mul, nystromCLM_apply] at ht
  field_simp
  linarith [ht]

/-- **(13.2.4)–(13.2.7), the Nyström method for the boundary integral equation of the second
kind.**  Let `k` be the continuous parametrized double-layer kernel on `C_p(L) = C(AddCircle L, ℝ)`,
let the quadrature rules converge at every continuous integrand with uniformly bounded absolute
weight sums, and assume — as the book does, quoting the literature — that `-π + K` is invertible on
`C_p(L)`.  Then there is a constant `c` such that, for all large `n`, the approximating equations
`(-π + K_n) ρ_n = f` are uniquely solvable, `‖(-π + K_n)⁻¹‖ ≤ c`, and

`‖ρ - ρ_n‖_∞ ≤ c ‖K ρ - K_n ρ‖_∞`.

The book says of this that "the error analysis for the above is straightforward from
Theorem 12.4.4", and so it is: this is `AtkinsonHan.Chapter12.theorem_12_4_4` at `λ = -π`, with the
sign absorbed by reading it for the kernel `-k`. -/
theorem equation_13_2_7 (k : C(AddCircle L × AddCircle L, ℝ)) {m : ℕ → ℕ}
    {w : ∀ n, Fin (m n) → ℝ} {x : ∀ n, Fin (m n) → AddCircle L} {W : ℝ}
    (hW : ∀ n, ∑ j, |w n j| ≤ W)
    (hQ : ∀ v : C(AddCircle L, ℝ), Tendsto (fun n => Quadrature.functional (w n) (x n) v) atTop
      (𝓝 (integralCLM volume v)))
    {e : C(AddCircle L, ℝ) ≃L[ℝ] C(AddCircle L, ℝ)}
    (he : (e : C(AddCircle L, ℝ) →L[ℝ] C(AddCircle L, ℝ))
      = (-π) • 1 + kernelCLM volume k) :
    ∃ c : ℝ, ∀ᶠ n in atTop, ∃ en : C(AddCircle L, ℝ) ≃L[ℝ] C(AddCircle L, ℝ),
      (en : C(AddCircle L, ℝ) →L[ℝ] C(AddCircle L, ℝ))
          = (-π) • 1 + nystromCLM (w n) (x n) k ∧
      ‖(en.symm : C(AddCircle L, ℝ) →L[ℝ] C(AddCircle L, ℝ))‖ ≤ c ∧
      ∀ f ρ ρn : C(AddCircle L, ℝ),
        ((-π) • 1 + kernelCLM volume k : C(AddCircle L, ℝ) →L[ℝ] C(AddCircle L, ℝ)) ρ = f →
        ((-π) • 1 + nystromCLM (w n) (x n) k :
          C(AddCircle L, ℝ) →L[ℝ] C(AddCircle L, ℝ)) ρn = f →
        ‖ρ - ρn‖ ≤ c * ‖kernelCLM volume k ρ - nystromCLM (w n) (x n) k ρ‖ := by
  have hker : ((-π) • 1 - kernelCLM volume (-k) : C(AddCircle L, ℝ) →L[ℝ] C(AddCircle L, ℝ))
      = (-π) • 1 + kernelCLM volume k := by rw [kernelCLM_neg, sub_neg_eq_add]
  have hnys : ∀ n, ((-π) • 1 - nystromCLM (w n) (x n) (-k) :
      C(AddCircle L, ℝ) →L[ℝ] C(AddCircle L, ℝ)) = (-π) • 1 + nystromCLM (w n) (x n) k := by
    intro n
    rw [nystromCLM_neg, sub_neg_eq_add]
  obtain ⟨c, hc⟩ := AtkinsonHan.Chapter12.theorem_12_4_4 (ν := volume)
    (neg_ne_zero.2 Real.pi_ne_zero) (-k) hW hQ (e := e) (by rw [hker]; exact he)
  refine ⟨c, ?_⟩
  filter_upwards [hc] with n hn
  obtain ⟨en, hencoe, hennorm, herr⟩ := hn
  refine ⟨en, by rw [hencoe, hnys n], hennorm, fun f ρ ρn hρ hρn => ?_⟩
  refine (herr f ρ ρn (by rw [hker]; exact hρ) (by rw [hnys n]; exact hρn)).trans ?_
  rw [kernelCLM_neg, nystromCLM_neg]
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) ?_
  · rw [neg_apply, neg_apply, ← neg_sub, norm_neg, neg_sub_neg]
  · exact le_trans (norm_nonneg _) hennorm

/-- **(13.2.4)–(13.2.5), the Nyström method with the periodic trapezoidal rule.**  The concrete
scheme of §13.2: the boundary integral is approximated by

`K_n ρ (t) = h ∑_{j < n} k (t, j h) ρ (j h)`, `h = L / n`,

the trapezoidal rule on the closed parameter curve, and the discrete equations
`(-π + K_n) ρ_n = f` are then uniquely solvable for all large `n` with uniformly bounded inverses
and `‖ρ - ρ_n‖_∞ ≤ c ‖K ρ - K_n ρ‖_∞`.

This is `equation_13_2_7` with its two quadrature hypotheses discharged:
`Quadrature.sum_abs_circleTrapezoid` bounds the absolute weight sums by `L` and
`Quadrature.tendsto_circleTrapezoid` is the Riemann sum theorem on the circle.  It is the form the
book actually computes with, and the kernel it applies to is `doubleLayerKernelCP`. -/
theorem equation_13_2_4 (k : C(AddCircle L × AddCircle L, ℝ))
    {e : C(AddCircle L, ℝ) ≃L[ℝ] C(AddCircle L, ℝ)}
    (he : (e : C(AddCircle L, ℝ) →L[ℝ] C(AddCircle L, ℝ))
      = (-π) • 1 + kernelCLM volume k) :
    ∃ c : ℝ, ∀ᶠ n in atTop, ∃ en : C(AddCircle L, ℝ) ≃L[ℝ] C(AddCircle L, ℝ),
      (en : C(AddCircle L, ℝ) →L[ℝ] C(AddCircle L, ℝ))
          = (-π) • 1 + nystromCLM (fun _ : Fin n => L / n)
            (fun j : Fin n => (((j : ℕ) * (L / n) : ℝ) : AddCircle L)) k ∧
      ‖(en.symm : C(AddCircle L, ℝ) →L[ℝ] C(AddCircle L, ℝ))‖ ≤ c ∧
      ∀ f ρ ρn : C(AddCircle L, ℝ),
        ((-π) • 1 + kernelCLM volume k : C(AddCircle L, ℝ) →L[ℝ] C(AddCircle L, ℝ)) ρ = f →
        ((-π) • 1 + nystromCLM (fun _ : Fin n => L / n)
          (fun j : Fin n => (((j : ℕ) * (L / n) : ℝ) : AddCircle L)) k :
          C(AddCircle L, ℝ) →L[ℝ] C(AddCircle L, ℝ)) ρn = f →
        ‖ρ - ρn‖ ≤ c * ‖kernelCLM volume k ρ - nystromCLM (fun _ : Fin n => L / n)
          (fun j : Fin n => (((j : ℕ) * (L / n) : ℝ) : AddCircle L)) k ρ‖ :=
  equation_13_2_7 k (W := L) (fun n => Quadrature.sum_abs_circleTrapezoid n)
    (fun v => by
      simpa only [integralCLM_apply, Quadrature.circleTrapezoid] using
        Quadrature.tendsto_circleTrapezoid v) he

/-! ### §13.2.3, the first kind equation and the logarithmic single layer operator -/

/-- **(13.2.31)–(13.2.32), the Fourier diagonalization of the logarithmic single layer
operator.**  The single layer operator of the unit circle, in the arclength parameter,

`A φ (t) = -(1 / π) ∫_0^{2 π} φ (s) log |2 e^(-1/2) sin ((t - s) / 2)| ds`,

acts on the Fourier modes `ψ_m (t) = e^(i m t)` by `A ψ_m = ψ_m / max {1, |m|}`, which is (13.2.37)
and, read off the Fourier expansion of `φ`, is (13.2.32).  It is the reason `A` is a bijection of
`H^0(2 π)` onto `H^1(2 π)`, and it is what makes the operator algebra of §13.3 elementary.

The book quotes this from Yan and Sloan; the proof here is
`Numlib/Analysis/Fourier/LogSingleLayer`, where the eigenvalue is the `m`-th Fourier coefficient of
`u ↦ log |2 e^(-1/2) sin (u / 2)|`.  The companion bound (13.2.33),
`‖A‖_{C_p → C_p} ≤ √(1 + π²/3)`, is a separate and harder statement, quoted by the book from
Atkinson, and is not proved here. -/
theorem equation_13_2_32 (m : ℤ) (t : ℝ) :
    -(1 / π) * ∫ s in (0 : ℝ)..(2 * π), Complex.exp (m * s * Complex.I)
        * (Real.log |2 * Real.exp (-(1 / 2)) * Real.sin ((t - s) / 2)| : ℂ)
      = Complex.exp (m * t * Complex.I) / max 1 |m| := by
  rw [← logSingleLayerC_fourier m t, logSingleLayerC, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [logSingleLayerKernel]
  push_cast
  ring

/-- **Exercise 13.3.1**: for a non-negative integer `k`, the first kind equation

`-(1 / π) ∫_0^{2 π} φ (s) log |2 e^(-1/2) sin ((t - s) / 2)| ds = cos (k t)`

is solved by `φ (t) = max {1, k} cos (k t)` — that is, by `k cos (k t)` when `k ≥ 1` and by the
constant `1` when `k = 0`.  A direct reading of `equation_13_2_32` on the real modes. -/
theorem exercise_13_3_1 (k : ℕ) (t : ℝ) :
    -(1 / π) * ∫ s in (0 : ℝ)..(2 * π), ((max 1 k : ℕ) : ℝ) * Real.cos (k * s)
        * Real.log |2 * Real.exp (-(1 / 2)) * Real.sin ((t - s) / 2)|
      = Real.cos (k * t) := by
  have hk : ((max 1 k : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.one_le_iff_ne_zero.1 (le_max_left 1 k))
  have h : logSingleLayer (fun s => ((max 1 k : ℕ) : ℝ) * Real.cos ((k : ℝ) * s)) t
      = Real.cos ((k : ℝ) * t) := by
    rw [logSingleLayer_const_mul, logSingleLayer_cos]
    field_simp
  rw [← h, logSingleLayer, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [logSingleLayerKernel]
  ring

end AtkinsonHan.Chapter13

