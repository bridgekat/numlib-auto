import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
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

## Not formalized here

* The identification of `K` with the boundary integral `∫_S ρ(Q) ∂/∂n_Q log |P - Q| dS_Q`, which
  needs a surface measure and a normal field on `S`; only the parametrized kernel is reachable, and
  that is `Chapter13/Section01`.
* The *concrete* trapezoidal rule `h ∑_{j<n} v (j h)` with `h = L / n`.  What is missing is its
  convergence for every continuous periodic integrand: a Riemann-sum theorem, which neither this
  library nor Mathlib has, and which `Numlib/Approximation/Quadrature` has no composite rule to
  state it for.  The convergence of the rules is therefore a hypothesis of `equation_13_2_7`,
  written exactly as Theorem 12.4.4 asks for it.  The *rate* — spectral convergence of the
  trapezoidal rule for a smooth periodic integrand — is Proposition 7.5.6 and needs the periodic
  Sobolev scale `H^s(2π)`; only the bound is stated.
* Exercise 13.2.5, that `‖K‖ = π` for a convex region; (13.2.14)–(13.2.23), the evaluation of the
  potential near the boundary; and (13.2.32), the Fourier diagonalization of the logarithmic
  single-layer operator.  See `plans/NumlibSurface/AtkinsonHan/Chapter13/Section02.toml`.
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

end AtkinsonHan.Chapter13
