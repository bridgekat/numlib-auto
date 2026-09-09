import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Numlib.Analysis.Fourier.LogSingleLayer
import Numlib.Approximation.CompositeQuadrature
import Mathlib.Topology.Instances.AddCircle.Real
import NumlibSurface.AtkinsonHan.Chapter12.Section04
import NumlibSurface.AtkinsonHan.Chapter13.Section01

/-!
# Atkinson–Han §13.2: the Nyström method for the boundary integral equation

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §13.2.

The interior Dirichlet problem for Laplace's equation on a planar region with smooth boundary `S`
is reformulated as the boundary integral equation of the second kind

`-π ρ(P) + ∫_S ρ(Q) ∂/∂n_Q log |P - Q| dS_Q = f(P)`,

and after a regular `C²` parametrization of `S` by arclength this is an ordinary integral equation
`(-π + K) ρ = f` on the space `C_p(L)` of continuous `L`-periodic functions, with a *continuous*
kernel: the parametrized double-layer kernel `Chapter13.doubleLayerKernelCP` extends continuously to
the diagonal, where by (13.1.34) its value is minus half the signed curvature.  Its sign is the
book's, so that the row integral `∫_0^L k(t, s) ds` is `-π`; substituting it for the abstract `k`
below therefore reproduces (13.1.32) and (13.2.3) as the book writes them, `(-π + K) ρ = f`, and not
their negatives.  The book's own words are that "the natural function space setting for
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
* `ellipseDoubleLayerKernel`, `example_13_2_1` and `example_13_2_1_peakingFactor` — (13.2.9), the
  collapse of the double layer kernel of an ellipse to a function of `(s + t) / 2` alone, and the
  peaking factor `p(a, b) = (max {a, b} / min {a, b})²` of that function.
* `example_13_2_3` — that the test solution `u(x, y) = x / (x² + y²)` of Example 13.2.3 is what the
  example says it is: harmonic away from the origin, and vanishing at infinity, so that it really
  is a solution of an *exterior* problem.  It is the Kelvin transform of the coordinate `x`.

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
* The numerical halves of Examples 13.2.1, 13.2.2 and 13.2.3, which are Tables 13.1–13.3 and
  Figures 13.1–13.5: measured errors of the Nyström method on one curve at a time, and not
  statements.  Example 13.2.2 is *only* that, and stays open; of Examples 13.2.1 and 13.2.3 the
  claims that are not measured numbers — the kernel identity (13.2.9) with its peaking factor, and
  the harmonicity and decay of the test solution — are stated.  The method Example 13.2.3
  illustrates, §13.2.2, rests on the boundary integral equation (13.2.24), which is (13.1.30) of
  the potential theory §13.1 skips, and on the splitting (13.2.25)–(13.2.30) of its right-hand
  side into the logarithmic single layer operator `A` — whose diagonalization *is* here,
  `equation_13_2_32` — and a smooth remainder; the splitting is an identity between integrals over
  `S`, so it needs the surface measure that `Chapter13/Section01` records as out of reach.  Its
  error analysis needs in addition the trigonometric interpolation and Euler–Maclaurin rates
  (13.2.36), (13.2.39), (13.2.41) and (13.2.43).
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

/-! ### Example 13.2.1: the ellipse -/

/-- **(13.2.9)**, the function `κ` of Example 13.2.1:

`κ(θ) = -a b / (2 (a² sin² θ + b² cos² θ))`.

For the ellipse `r(t) = (a cos t, b sin t)` the parametrized double layer kernel is
`k(t, s) = κ((s + t) / 2)` (`example_13_2_1`): it depends on the two parameters through their mean
alone.  On the circle `a = b` it is the constant `-1 / (2 a)`, which for `a = 1` is the `-1/2` of
`Chapter13.doubleLayerKernel_circle_self`. -/
noncomputable def ellipseDoubleLayerKernel (a b θ : ℝ) : ℝ :=
  -(a * b) / (2 * (a ^ 2 * Real.sin θ ^ 2 + b ^ 2 * Real.cos θ ^ 2))

/-- **Example 13.2.1**, the kernel identity (13.2.9).  For the ellipse `r(t) = (a cos t, b sin t)`
the double layer kernel (13.1.33) collapses to a function of the mean parameter alone,

`k(t, s) = κ((s + t) / 2)`,  `κ(θ) = -a b / (2 (a² sin² θ + b² cos² θ))`,

which is what makes the integral equation (13.2.10) cheap to assemble: one univariate function
supplies the whole matrix.  The identity is algebraic — no positivity of `a` or `b` is used — and
holds on the diagonal too, where it is (13.1.34).

The hypothesis is that `t` and `s` are the *same* parameter or parameters of *distinct* points of
the ellipse: `sin ((t - s) / 2) = 0` with `t ≠ s` means `s - t` is a nonzero multiple of `2 π`, and
there `doubleLayerKernel` is `0`, because it divides the vanishing chord by `s - t`.  That is the
same phenomenon `Chapter13.doubleLayerKernel_add_period` records, and the reason §13.2 works on
`AddCircle L` rather than on the line. -/
theorem example_13_2_1 (a b : ℝ) {t s : ℝ} (hts : t = s ∨ Real.sin ((t - s) / 2) ≠ 0) :
    doubleLayerKernel (fun u => -(a * Real.sin u)) (fun u => b * Real.cos u)
        (fun u => -(a * Real.cos u)) (fun u => -(b * Real.sin u)) t s
      = ellipseDoubleLayerKernel a b ((s + t) / 2) := by
  have hξ : ∀ x : ℝ, HasDerivAt (fun u => a * Real.cos u) (-(a * Real.sin x)) x := fun x => by
    simpa using (Real.hasDerivAt_cos x).const_mul a
  have hη : ∀ x : ℝ, HasDerivAt (fun u => b * Real.sin u) (b * Real.cos x) x := fun x =>
    (Real.hasDerivAt_sin x).const_mul b
  have hξ' : ∀ x : ℝ, HasDerivAt (fun u => -(a * Real.sin u)) (-(a * Real.cos x)) x := fun x =>
    ((Real.hasDerivAt_sin x).const_mul a).neg
  have hη' : ∀ x : ℝ, HasDerivAt (fun u => b * Real.cos u) (-(b * Real.sin x)) x := fun x => by
    simpa using (Real.hasDerivAt_cos x).const_mul b
  rcases hts with rfl | hsin
  · rw [equation_13_1_34, ellipseDoubleLayerKernel, show (t + t) / 2 = t by ring]
    congr 1
    · linear_combination (-(a * b)) * Real.sin_sq_add_cos_sq t
    · ring
  · have hst : s ≠ t := fun h => hsin (by rw [h, sub_self]; simp)
    rw [equation_13_1_33 hξ hξ' hη hη' (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) hst,
      ellipseDoubleLayerKernel]
    set θ : ℝ := (s + t) / 2 with hθ
    set d : ℝ := (t - s) / 2 with hd
    have htd : t = θ + d := by rw [hθ, hd]; ring
    have hsd : s = θ - d := by rw [hθ, hd]; ring
    rw [htd, hsd, Real.cos_add, Real.cos_sub, Real.sin_add, Real.sin_sub]
    have hnum : b * (Real.cos θ * Real.cos d + Real.sin θ * Real.sin d) *
          (a * (Real.cos θ * Real.cos d - Real.sin θ * Real.sin d)
            - a * (Real.cos θ * Real.cos d + Real.sin θ * Real.sin d))
        - -(a * (Real.sin θ * Real.cos d - Real.cos θ * Real.sin d)) *
          (b * (Real.sin θ * Real.cos d + Real.cos θ * Real.sin d)
            - b * (Real.sin θ * Real.cos d - Real.cos θ * Real.sin d))
        = Real.sin d ^ 2 * (-(2 * (a * b))) := by
      linear_combination (-(2 * a * b * Real.sin d ^ 2)) * Real.sin_sq_add_cos_sq θ
    have hden : (a * (Real.cos θ * Real.cos d - Real.sin θ * Real.sin d)
            - a * (Real.cos θ * Real.cos d + Real.sin θ * Real.sin d)) ^ 2
        + (b * (Real.sin θ * Real.cos d + Real.cos θ * Real.sin d)
            - b * (Real.sin θ * Real.cos d - Real.cos θ * Real.sin d)) ^ 2
        = Real.sin d ^ 2 * (4 * (a ^ 2 * Real.sin θ ^ 2 + b ^ 2 * Real.cos θ ^ 2)) := by
      ring
    rw [hnum, hden, mul_div_mul_left _ _ (pow_ne_zero 2 hsin),
      show -(2 * (a * b)) = 2 * -(a * b) by ring,
      show (4 : ℝ) * (a ^ 2 * Real.sin θ ^ 2 + b ^ 2 * Real.cos θ ^ 2)
        = 2 * (2 * (a ^ 2 * Real.sin θ ^ 2 + b ^ 2 * Real.cos θ ^ 2)) by ring,
      mul_div_mul_left _ _ two_ne_zero]

/-- **Example 13.2.1**, the peaking factor.  The book measures how hard the equation (13.2.10) is
to solve by

`p(a, b) = max |k(t, s)| / min |k(t, s)| = (max {a, b} / min {a, b})²`,

so `p(1, 2) = 4`, `p(1, 5) = 25` and `p(1, 8) = 64`: the more elongated the ellipse, the more
peaked the kernel and the larger the `n` needed for a given accuracy, which is what Table 13.1
shows.  The extremes are attained at `θ = 0` and `θ = π / 2`, the ends of the two axes, because
`a² sin² θ + b² cos² θ` runs over `[min {a, b}², max {a, b}²]`. -/
theorem example_13_2_1_peakingFactor {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IsGreatest (Set.range fun θ : ℝ => |ellipseDoubleLayerKernel a b θ|)
        (a * b / (2 * min a b ^ 2)) ∧
      IsLeast (Set.range fun θ : ℝ => |ellipseDoubleLayerKernel a b θ|)
        (a * b / (2 * max a b ^ 2)) ∧
      a * b / (2 * min a b ^ 2) / (a * b / (2 * max a b ^ 2)) = (max a b / min a b) ^ 2 := by
  have hab : 0 < a * b := mul_pos ha hb
  have hmin : 0 < min a b := lt_min ha hb
  have hmax : 0 < max a b := lt_of_lt_of_le ha (le_max_left a b)
  have hlb : ∀ θ : ℝ, min a b ^ 2 ≤ a ^ 2 * Real.sin θ ^ 2 + b ^ 2 * Real.cos θ ^ 2 := by
    intro θ
    have h1 : min a b ^ 2 ≤ a ^ 2 := by nlinarith [min_le_left a b, hmin]
    have h2 : min a b ^ 2 ≤ b ^ 2 := by nlinarith [min_le_right a b, hmin]
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ), sq_nonneg (Real.cos θ),
      mul_nonneg (sub_nonneg.2 h1) (sq_nonneg (Real.sin θ)),
      mul_nonneg (sub_nonneg.2 h2) (sq_nonneg (Real.cos θ))]
  have hub : ∀ θ : ℝ, a ^ 2 * Real.sin θ ^ 2 + b ^ 2 * Real.cos θ ^ 2 ≤ max a b ^ 2 := by
    intro θ
    have h1 : a ^ 2 ≤ max a b ^ 2 := by nlinarith [le_max_left a b, ha]
    have h2 : b ^ 2 ≤ max a b ^ 2 := by nlinarith [le_max_right a b, hb]
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ), sq_nonneg (Real.cos θ),
      mul_nonneg (sub_nonneg.2 h1) (sq_nonneg (Real.sin θ)),
      mul_nonneg (sub_nonneg.2 h2) (sq_nonneg (Real.cos θ))]
  have hDpos : ∀ θ : ℝ, 0 < a ^ 2 * Real.sin θ ^ 2 + b ^ 2 * Real.cos θ ^ 2 := fun θ =>
    lt_of_lt_of_le (pow_pos hmin 2) (hlb θ)
  have habs : ∀ θ : ℝ, |ellipseDoubleLayerKernel a b θ|
      = a * b / (2 * (a ^ 2 * Real.sin θ ^ 2 + b ^ 2 * Real.cos θ ^ 2)) := by
    intro θ
    rw [ellipseDoubleLayerKernel, abs_div, abs_neg, abs_of_pos hab,
      abs_of_pos (by have := hDpos θ; positivity)]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rcases le_total a b with h | h
    · exact ⟨π / 2, by
        simp only [habs, Real.sin_pi_div_two, Real.cos_pi_div_two, min_eq_left h]; norm_num⟩
    · exact ⟨0, by simp only [habs, Real.sin_zero, Real.cos_zero, min_eq_right h]; norm_num⟩
  · rintro _ ⟨θ, rfl⟩
    simp only [habs]
    rw [div_le_div_iff₀ (by have := hDpos θ; positivity) (by positivity)]
    nlinarith [hlb θ, hab.le]
  · rcases le_total a b with h | h
    · exact ⟨0, by simp only [habs, Real.sin_zero, Real.cos_zero, max_eq_right h]; norm_num⟩
    · exact ⟨π / 2, by
        simp only [habs, Real.sin_pi_div_two, Real.cos_pi_div_two, max_eq_left h]; norm_num⟩
  · rintro _ ⟨θ, rfl⟩
    simp only [habs]
    rw [div_le_div_iff₀ (by positivity) (by have := hDpos θ; positivity)]
    nlinarith [hub θ, hab.le]
  · field_simp

/-! ### Example 13.2.3: the test solution of the exterior Neumann problem -/

/-- **Example 13.2.3**, the choice of test solution.  The example solves the exterior Neumann
problem outside an ellipse with boundary data generated from

`u(x, y) = x / (x² + y²)`,

and says of it exactly two things: that it is harmonic, and that it tends to `0` at infinity — the
condition at infinity an exterior harmonic problem carries.  Both are stated here, together with
the identification of `u` as the Kelvin transform of the coordinate `x`: `u = kelvin re`, since
inversion `T z = z / ‖z‖²` sends `z` to `z / (x² + y²)`.  Harmonicity is then §13.1.2's
`kelvin_harmonic` — the real part of the identity is harmonic and the transform preserves
harmonicity — which is what the transform is in the book for, and the decay is
`|x| / (x² + y²) ≤ 1 / ‖(x, y)‖`.

The rest of the example is Table 13.3 and Figure 13.5, measured errors of the Nyström method for
one ellipse; and the method itself is §13.2.2, whose boundary integral equation is derived from the
single layer potential and its normal derivative, which is the potential theory this chapter
skips. -/
theorem example_13_2_3 :
    (∀ z : ℂ, kelvin Complex.re z = z.re / ‖z‖ ^ 2) ∧
      (∀ z : ℂ, z ≠ 0 → InnerProductSpace.HarmonicAt (kelvin Complex.re) z) ∧
      Tendsto (kelvin Complex.re) (cocompact ℂ) (𝓝 0) := by
  have hval : ∀ z : ℂ, kelvin Complex.re z = z.re / ‖z‖ ^ 2 := by
    intro z
    rw [kelvin, Complex.div_ofReal_re]
  refine ⟨hval, fun z hz => kelvin_harmonic hz (analyticAt_id (𝕜 := ℂ)).harmonicAt_re, ?_⟩
  have hnorm : Tendsto (fun z : ℂ => ‖z‖) (cocompact ℂ) atTop := tendsto_norm_cocompact_atTop
  have h1 : Tendsto (fun z : ℂ => ‖z‖⁻¹) (cocompact ℂ) (𝓝 0) := tendsto_inv_atTop_zero.comp hnorm
  refine squeeze_zero_norm' ?_ h1
  filter_upwards [hnorm.eventually_gt_atTop 0] with z hz
  rw [hval z, Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖z‖ ^ 2),
    div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ hz]
  calc |z.re| * ‖z‖ ≤ ‖z‖ * ‖z‖ :=
        mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm z) (norm_nonneg z)
    _ = ‖z‖ ^ 2 := by ring

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

