import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.MetricSpace.Holder
import Numlib.Analysis.Normed.Operator.BanachSteinhaus
import Numlib.Analysis.Normed.Module.BestApprox
import Numlib.Approximation.Chebyshev
import Numlib.Approximation.Jackson
import Numlib.Approximation.LeastSquares
import Numlib.Approximation.OrthogonalPolynomial
import Numlib.Approximation.Trigonometric
import Numlib.Approximation.TrigonometricInterpolation
import Numlib.Krylov.OrthogonalPolynomials
import NumlibSurface.AtkinsonHan.Chapter03.Section06

/-!
# Atkinson–Han §3.7: uniform error bounds

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §3.7.

The section's two abstract ingredients are formalized here:

* the **Lebesgue lemma** `‖f − 𝓟f‖ ≤ (1 + ‖𝓟‖) ‖f − q‖` for a bounded projection `𝓟` and any `q`
  in its range, which is the common form of (3.7.11), (3.7.14) and (3.7.21); and
* the **non-convergence lemma**: if the norms of a sequence of bounded operators on a Banach
  space are unbounded, some vector is not the limit of its images. This is the Banach–Steinhaus
  argument that produces a continuous periodic function whose Fourier partial sums diverge.

## Main results

* `lebesgue_lemma`, `lebesgue_lemma_iInf`, `lebesgue_lemma_one_sub`.
* `exists_not_tendsto_of_not_bddAbove`.
* `HolderClass`, `HolderClassIcc` — the function spaces `C_p^{k,α}(2π)` and `C^{k,α}[−1, 1]` that
  Theorems 3.7.1–3.7.2 speak about, as definitions only. The underlying space `C_p(2π)` is §3.6's
  `IsPeriodicCont` and `PeriodicCont`, first needed there by Example 3.6.8.
* `equation_3_7_5` — `‖f - 𝓕ₙ f‖_{L²} ≤ √(2π) ‖f - 𝓕ₙ f‖_∞`, the `L²` norm being taken
  against the standard measure of the circle, of total mass `2π`.
* `equation_3_7_6`, `equation_3_7_8`, `equation_3_7_9` — the Dirichlet-kernel representation of
  the Fourier projection `𝓕ₙ`, the closed form of `Dₙ`, and `‖𝓕ₙ‖ = Lₙ`;
  `norm_fourierProj_asymptotics` is the two-sided `Lₙ ≍ log n` that stands in for (3.7.10), and
  `exists_not_tendsto_fourierProj` is what the book draws from it: a continuous periodic function
  whose Fourier series does not converge uniformly.
* `theorem_3_7_1` — **Jackson's theorem** for `C_p^{k,α}(2π)`, a specialization of the backbone's
  `Jackson.infDist_le_of_holder_deriv'`; `equation_3_7_11` and `equation_3_7_12` combine it with
  the Lebesgue lemma to give the rate `c_k log n / n^{k+α}` for the Fourier partial sums.
* `theorem_3_7_2` — **Jackson's theorem** for `C^{k,α}[−1, 1]`, the polynomial case, from the
  backbone's `Jackson.infDist_le_of_holder_poly`: the transfer through `x = cos θ` and the
  recursion in the degree, which for algebraic polynomials loses nothing.
* `theorem_3_7_3`, `theorem_3_7_3_confluent` — the Christoffel–Darboux identity for the
  orthonormal polynomials of a weight, in the quotient form the book states and in its confluent
  case `x = t`.
* `equation_3_7_19` — the Dirichlet-kernel form of the trigonometric interpolatory projection
  `𝓘ₙ` at the equispaced nodes; `norm_trigInterpCLM_bound` is Rivlin's bound on its operator norm,
  `‖𝓘ₙ‖ ≤ 2 + (2/π) log (2 n + 1)`, and `equation_3_7_21`, `equation_3_7_22` are the uniform
  error bounds that follow from it and Jackson's theorem.
* `not_equation_3_7_20` — the bound `‖𝓘ₙ‖ ≤ 1 + (2/π) log n` as (3.7.20) prints it is false: at
  `n = 1` its right-hand side is `1` and `‖𝓘₁‖ ≥ 5/3`.
* `equation_3_7_13`–`equation_3_7_17` — the least-squares projection `P_N` of `C[−1, 1]` onto the
  span of an orthonormal system of continuous functions, as the integral operator of the
  reproducing kernel `K(x, t) = ∑ₙ pₙ(x) pₙ(t)`, with `‖P_N‖ = max_x ∫ |K(x, t)| dt`.
* `example_3_7_4` — for the Chebyshev weight, `‖P_N‖` is *exactly* the `N`-th Lebesgue constant
  `L_N` of the Fourier projection; `norm_chebyshevProj_asymptotics` transports the two-sided
  `L_N ≍ log N` to it.

## Not formalized here

* (3.7.10), Zygmund's sharp asymptotics `Lₙ = (4/π²) log n + O(1)`: the backbone proves the two
  halves with different constants, `(4/π²) log n ≤ Lₙ ≤ 1 + log (2 n + 1)`, which is what the
  divergence argument and the convergence rate consume, so `norm_fourierProj_asymptotics` carries
  that name rather than the equation's.
* the last step of **Example 3.7.4**, `‖P_N‖ = (4/π²) log N + 𝒪(1)`: `example_3_7_4` proves the
  exact identity `‖P_N‖ = L_N` that the book's derivation reaches, and the asymptotics it then
  quotes are (3.7.10), which is not proved here either.
* (3.7.20) exactly as printed, `‖𝓘ₙ‖ ≤ 1 + (2/π) log n`: it is false, and `not_equation_3_7_20`
  proves it false. The sharp true statement replaces `n` by the number `2 n + 1` of nodes, and
  even that leaves only about `0.04` between its two sides; the backbone's
  `norm_trigInterpCLM_le`, quoted here as `norm_trigInterpCLM_bound`, keeps the sharp coefficient
  `2/π` and pays an additive `2` instead of `1`.
-/

open Filter Topology

namespace AtkinsonHan.Chapter03

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-! ### The Lebesgue lemma -/

/-- **Lebesgue lemma**, pointwise form. For a bounded projection `𝓟` and any `q` in its range,
`‖u − 𝓟u‖ ≤ (1 + ‖𝓟‖) ‖u − q‖`. This is the shape of Atkinson–Han (3.7.11), (3.7.14) and
(3.7.21): the error of a projection method is within `1 + ‖𝓟‖` of the best approximation error
from the projection space. -/
theorem lebesgue_lemma (P : V →L[𝕜] V) (hP : IsIdempotentElem P) (u : V) {q : V}
    (hq : q ∈ LinearMap.range (P : V →ₗ[𝕜] V)) : ‖u - P u‖ ≤ (1 + ‖P‖) * ‖u - q‖ :=
  norm_sub_apply_le_of_isIdempotentElem_of_mem P hP u hq

/-- **Lebesgue lemma**, in terms of the best approximation error from the projection space. -/
theorem lebesgue_lemma_iInf (P : V →L[𝕜] V) (hP : IsIdempotentElem P) (u : V) :
    ‖u - P u‖ ≤ (1 + ‖P‖) *
      ⨅ w : (LinearMap.range (P : V →ₗ[𝕜] V) : Set V), ‖u - (w : V)‖ := by
  have h := norm_sub_apply_le_of_isIdempotentElem P hP u
  rw [Metric.infDist_eq_iInf] at h
  simpa only [dist_eq_norm] using h

/-- The sharper constant `‖I − 𝓟‖` in place of `1 + ‖𝓟‖`. -/
theorem lebesgue_lemma_one_sub (P : V →L[𝕜] V) (hP : IsIdempotentElem P) (u : V) :
    ‖u - P u‖ ≤ ‖(1 : V →L[𝕜] V) - P‖ *
      ⨅ w : (LinearMap.range (P : V →ₗ[𝕜] V) : Set V), ‖u - (w : V)‖ := by
  have h := norm_sub_apply_le_of_isIdempotentElem' P hP u
  rw [Metric.infDist_eq_iInf] at h
  simpa only [dist_eq_norm] using h

/-! ### Non-convergence from unbounded operator norms -/

/-- If the operator norms `‖𝓟ₙ‖` are unbounded, then `𝓟ₙ f → f` fails for some `f`. Applied to
the Fourier projections `𝓕ₙ` on `C_p(2π)`, whose norms are the Lebesgue constants
`Lₙ = (4/π²) log n + O(1)` by (3.7.10), this is the paragraph after (3.7.10): there is a
continuous periodic function whose Fourier series does not converge uniformly to it.

It is the backbone's `ContinuousLinearMap.exists_not_tendsto_of_not_bddAbove` at `L = id`. -/
theorem exists_not_tendsto_of_not_bddAbove [CompleteSpace V] (P : ℕ → V →L[𝕜] V)
    (h : ¬ BddAbove (Set.range fun n => ‖P n‖)) :
    ∃ f : V, ¬ Tendsto (fun n => P n f) atTop (𝓝 f) :=
  ContinuousLinearMap.exists_not_tendsto_of_not_bddAbove h (ContinuousLinearMap.id 𝕜 V)

/-! ### The Hölder classes of Theorems 3.7.1 and 3.7.2

Definitions only. The theorems themselves wait on trigonometric approximation. The space
`C_p(2π)` on which they live — `IsPeriodicCont`, `PeriodicCont` and the passage between them — is
§3.6's, where Example 3.6.8 first needs it. -/

section Spaces

open Real NNReal

/-- `C_p^{k,α}(2π)` with constant `M`: `k` times continuously differentiable with `M`-Hölder
`k`-th derivative of exponent `α`. -/
def HolderClass (k : ℕ) (α M : ℝ≥0) (g : ℝ → ℝ) : Prop :=
  IsPeriodicCont g ∧ ContDiff ℝ k g ∧ HolderWith M α (iteratedDeriv k g)

/-- The same class on `[−1, 1]`, used for the polynomial half of Theorem 3.7.2. -/
def HolderClassIcc (k : ℕ) (α M : ℝ≥0) (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ k f (Set.Icc (-1) 1) ∧
    HolderOnWith M α (iteratedDerivWithin k f (Set.Icc (-1) 1)) (Set.Icc (-1) 1)

end Spaces

/-! ### (3.7.6)–(3.7.9): the Fourier projection and the Lebesgue constants -/

section FourierProjection

open Real _root_.PeriodicCont

/-- **(3.7.6)**: the `n`-th partial sum of the Fourier series of `f ∈ C_p(2π)` is the integral of
`f` against the Dirichlet kernel, `𝓕ₙ f (x) = (1/π) ∫_{-π}^{π} Dₙ(x - y) f(y) dy`. -/
theorem equation_3_7_6 (n : ℕ) (f : PeriodicCont) (x : ℝ) :
    fourierProj n f ↑x = 1 / π * ∫ y in -π..π, dirichletKernel n (x - y) * f ↑y := by
  have hf : Function.Periodic (fun t : ℝ => f ↑t) (2 * π) := fun t => by
    simp only []
    rw [AddCircle.coe_add_period]
  have hper : Function.Periodic (fun y : ℝ => dirichletKernel n (x - y) * f ↑y) (2 * π) := by
    intro y
    have h1 : dirichletKernel n (x - (y + 2 * π)) = dirichletKernel n (x - y) := by
      rw [show x - (y + 2 * π) = (x - y) - 2 * π by ring]
      exact (dirichletKernel_periodic n).sub_eq (x - y)
    have h2 : f ((y + 2 * π : ℝ) : AddCircle (2 * π)) = f ((y : ℝ) : AddCircle (2 * π)) := hf y
    simp only []
    rw [h1, h2]
  have hshift : (∫ y in -π..π, dirichletKernel n (x - y) * f ↑y)
      = ∫ r in -π..π, dirichletKernel n r * f ↑(x + r) := by
    have h1 := hper.intervalIntegral_add_eq (-π) (x + -π)
    rw [show -π + 2 * π = π by ring, show x + -π + 2 * π = x + π by ring] at h1
    rw [h1, ← intervalIntegral.integral_comp_add_left
      (fun y : ℝ => dirichletKernel n (x - y) * f ↑y) x]
    refine intervalIntegral.integral_congr fun r _ => ?_
    rw [show x - (x + r) = -r by ring, dirichletKernel_neg]
  rw [hshift, fourierProj_apply, integral_addCircle_eq
    (fun y => fourierKernel n (↑x, y) * f y) x, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun r _ => ?_
  have hsub : ((↑(x + r) : AddCircle (2 * π)) - ↑x) = ((r : ℝ) : AddCircle (2 * π)) := by
    have h : ((↑(x + r) : AddCircle (2 * π))) = (↑x : AddCircle (2 * π)) + ↑r := rfl
    rw [h, add_sub_cancel_left]
  simp only [fourierKernel_apply, hsub, dirichletCM_coe]
  field_simp

/-- **(3.7.7)–(3.7.8)**: the Dirichlet kernel is `Dₙ(θ) = 1/2 + ∑_{j=1}^{n} cos (j θ)`, and away
from the multiples of `2π` it is `sin ((n + 1/2) θ) / (2 sin (θ/2))`. -/
theorem equation_3_7_8 (n : ℕ) {t : ℝ} (ht : Real.sin (t / 2) ≠ 0) :
    dirichletKernel n t = 1 / 2 + ∑ j ∈ Finset.Icc 1 n, Real.cos (j * t) ∧
      dirichletKernel n t = Real.sin ((n + 1 / 2) * t) / (2 * Real.sin (t / 2)) :=
  ⟨dirichletKernel_apply n t, dirichletKernel_eq_sin_div ht⟩

/-- **(3.7.9)**: `𝓕ₙ : C_p(2π) → 𝕋ₙ` is a bounded projection whose operator norm is the `n`-th
Lebesgue constant `Lₙ = (2/π) ∫_0^π |Dₙ(y)| dy`. -/
theorem equation_3_7_9 (n : ℕ) :
    ‖fourierProj n‖ = 2 / π * ∫ t in (0 : ℝ)..π, |dirichletKernel n t| := by
  rw [norm_fourierProj, lebesgueConstant_eq]

/-- The Lebesgue constants are of exact order `log n`: this is the two-sided bound that the sharp
asymptotics (3.7.10) `Lₙ = (4/π²) log n + 𝓞(1)` of Zygmund refine. The lower half is what makes
`{‖𝓕ₙ‖}` unbounded, and so — by `exists_not_tendsto_of_not_bddAbove` — produces a continuous
periodic function whose Fourier series does not converge uniformly; the upper half is what the
convergence rate (3.7.12) consumes. -/
theorem norm_fourierProj_asymptotics (n : ℕ) :
    4 / π ^ 2 * Real.log n ≤ ‖fourierProj n‖ ∧
      ‖fourierProj n‖ ≤ 1 + Real.log (2 * (n : ℝ) + 1) := by
  rw [norm_fourierProj]
  exact ⟨log_le_lebesgueConstant n, lebesgueConstant_le n⟩

/-- **(3.7.5)**: `‖f - 𝓕ₙ f‖_{L²(-π, π)} ≤ √(2π) ‖f - 𝓕ₙ f‖_∞` for a continuous `2π`-periodic `f`.

The `L²` norm is taken against the standard measure of `ℝ/2πℤ`, which has total mass `2π` and is
the Lebesgue measure of one period; the constant `√(2π)` is the square root of that mass, and the
inequality holds for the difference `f - q` with any `q`, not just `q = 𝓕ₙ f`. -/
theorem equation_3_7_5 (n : ℕ) (f : PeriodicCont) :
    ‖ContinuousMap.toLp (E := ℝ) 2 (MeasureTheory.volume : MeasureTheory.Measure
        (AddCircle (2 * π))) ℝ (f - fourierProj n f)‖
      ≤ √(2 * π) * ‖f - fourierProj n f‖ := by
  have h2pi : (0 : ℝ) ≤ 2 * π := by positivity
  have hmass : (MeasureTheory.measureUnivNNReal
      (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (2 * π))) : ℝ) = 2 * π := by
    rw [MeasureTheory.measureUnivNNReal, AddCircle.measure_univ, ENNReal.ofReal,
      ENNReal.toNNReal_coe, Real.coe_toNNReal _ h2pi]
  have hop : ‖(ContinuousMap.toLp (E := ℝ) 2 (MeasureTheory.volume : MeasureTheory.Measure
      (AddCircle (2 * π))) ℝ)‖ ≤ √(2 * π) := by
    refine (ContinuousMap.toLp_norm_le (E := ℝ) (p := 2) (𝕜 := ℝ)
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (2 * π))))).trans ?_
    rw [Real.sqrt_eq_rpow, hmass]
    norm_num
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  exact mul_le_mul_of_nonneg_right hop (norm_nonneg _)

/-- **The Fourier series of a continuous periodic function need not converge uniformly.** The
Lebesgue constants `Lₙ = ‖𝓕ₙ‖` grow like `log n`, so they are unbounded, and
`exists_not_tendsto_of_not_bddAbove` produces an `f ∈ C_p(2π)` with `𝓕ₙ f ↛ f`. This is the point
[han2009theoretical] draw from (3.7.10). -/
theorem exists_not_tendsto_fourierProj :
    ∃ f : PeriodicCont, ¬ Tendsto (fun n => fourierProj n f) atTop (𝓝 f) := by
  refine exists_not_tendsto_of_not_bddAbove (fun n => fourierProj n) fun hbd => ?_
  obtain ⟨C, hC⟩ := hbd
  have hlog : Tendsto (fun n : ℕ => 4 / π ^ 2 * Real.log n) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity)
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨n, hn⟩ := (hlog.eventually_gt_atTop C).exists
  exact absurd (hC ⟨n, rfl⟩) (not_le.2 (lt_of_lt_of_le hn (norm_fourierProj_asymptotics n).1))

end FourierProjection

/-! ### §3.7.3, (3.7.19): the trigonometric interpolatory projection -/

section TrigonometricInterpolation

open Real _root_.PeriodicCont

/-- **(3.7.19)**: the trigonometric interpolant of `f ∈ C_p(2π)` at the `2 n + 1` equispaced nodes
`xⱼ = 2π j/(2 n + 1)` of (3.2.16) is

`𝓘ₙ f (x) = (2/(2 n + 1)) ∑_{j=0}^{2n} Dₙ(x - xⱼ) f(xⱼ)`,

the discrete analogue of the Dirichlet-kernel formula (3.7.6) for the Fourier projection: the
cardinal functions of the interpolation problem are the recentred kernels
`2 Dₙ(· - xⱼ)/(2 n + 1)` (Exercise 3.7.5).

The bound on the operator norm that the book pairs it with is `norm_trigInterpCLM_bound`; see
`not_equation_3_7_20` for why it is not the one (3.7.20) prints. -/
theorem equation_3_7_19 (n : ℕ) (f : PeriodicCont) (x : ℝ) :
    trigInterpCLM (2 * π) n f ↑x
      = 2 / (2 * (n : ℝ) + 1) *
        ∑ j : Fin (2 * n + 1),
          dirichletKernel n (x - (j : ℕ) * (2 * π) / (2 * n + 1)) *
            f (trigInterpNode (2 * π) n j) :=
  trigInterpCLM_coe_apply n f x

end TrigonometricInterpolation

/-! ### Theorem 3.7.1 and (3.7.11)–(3.7.12): Jackson's theorem and the Fourier series -/

section JacksonTheorem

open Real NNReal _root_.PeriodicCont

set_option linter.unusedVariables false in
/-- **Theorem 3.7.1** (Jackson's theorem). Let `g ∈ C_p^{k,α}(2π)`: a `2π`-periodic function with
`k` continuous derivatives whose `k`-th derivative satisfies the Hölder condition
`|g⁽ᵏ⁾(θ₁) - g⁽ᵏ⁾(θ₂)| ≤ Mₖ |θ₁ - θ₂|^α` for some `Mₖ > 0` and some `α ∈ (0, 1]`. Then the error in
the best approximation `qₙ` to `g` from `𝕋ₙ` satisfies

`max_θ |g(θ) - qₙ(θ)| ≤ c^{k+1} Mₖ / n^{k+α}`,  `c = 1 + π²/2`.

The hypothesis `0 < α` is the book's and is not needed: the bound holds for `α = 0` too, where it
says that a function with bounded oscillation is approximated within a constant. -/
theorem theorem_3_7_1 {k n : ℕ} {α M : ℝ≥0} (hα0 : 0 < α) (hα1 : α ≤ 1) (hn : 1 ≤ n)
    {g : ℝ → ℝ} (hg : HolderClass k α M g) :
    Metric.infDist (PeriodicCont.ofIsPeriodicCont hg.1)
        (trigPolyLE (2 * π) n : Set C(AddCircle (2 * π), ℝ))
      ≤ (1 + π ^ 2 / 2) ^ (k + 1) * (M : ℝ) / (n : ℝ) ^ ((k : ℝ) + (α : ℝ)) := by
  obtain ⟨hper, hcd, hhol⟩ := hg
  have hlift : _root_.Jackson.lift (PeriodicCont.ofIsPeriodicCont hper) = g :=
    funext fun x => PeriodicCont.ofIsPeriodicCont_coe hper x
  refine _root_.Jackson.infDist_le_of_holder_deriv' (D := fun j => iteratedDeriv j g) hn ?_ ?_ ?_
    M.coe_nonneg α.coe_nonneg (by exact_mod_cast hα1) ?_
  · rw [iteratedDeriv_zero, hlift]
  · exact fun j hj => hcd.continuous_iteratedDeriv j (by exact_mod_cast hj)
  · intro j hj x
    have hdiff : Differentiable ℝ (iteratedDeriv j g) :=
      hcd.differentiable_iteratedDeriv j (by exact_mod_cast hj)
    have h := (hdiff x).hasDerivAt
    rwa [← iteratedDeriv_succ] at h
  · intro u v
    have h := hhol.dist_le u v
    rwa [Real.dist_eq, Real.dist_eq] at h

set_option linter.unusedVariables false in
/-- **Theorem 3.7.2** (Jackson's theorem, polynomial case). Let `f ∈ C^{k,α}[−1, 1]`: `k` times
continuously differentiable on `[−1, 1]`, with `|f⁽ᵏ⁾(x₁) − f⁽ᵏ⁾(x₂)| ≤ Mₖ |x₁ − x₂|^α` there for
some `Mₖ > 0` and some `α ∈ (0, 1]`. Then for `n > k` the error in the best approximation `pₙ` to
`f` from `ℙₙ` satisfies

`max_{−1 ≤ x ≤ 1} |f(x) − pₙ(x)| ≤ d_k c^{k+1} Mₖ / n^{k+α}`,  `c = 1 + π²/2`,

where `d_k` is any number with `d_k ≥ n^{k+α} / (n (n−1) ⋯ (n−k+1) (n−k)^α)`.

The `k`-th derivative is `iteratedDerivWithin k f [−1, 1]`, the one-sided derivative at the two
endpoints, which is what `ContDiffOn` on a closed interval provides; the book writes `f⁽ᵏ⁾`.

As with Theorem 3.7.1, the hypothesis `0 < α` is the book's and is not used. The backbone proves
the smaller constant `(π²/2)^{k+1}` in place of `c^{k+1}`; see
`Jackson.infDist_le_of_holder_poly`. -/
theorem theorem_3_7_2 {k n : ℕ} {α M d : ℝ≥0} (hα0 : 0 < α) (hα1 : α ≤ 1) (hkn : k < n)
    {f : ℝ → ℝ} (hf : HolderClassIcc k α M f)
    (hd : (n : ℝ) ^ ((k : ℝ) + (α : ℝ)) /
        ((∏ i ∈ Finset.range k, ((n : ℝ) - i)) * ((n : ℝ) - k) ^ (α : ℝ)) ≤ (d : ℝ)) :
    Metric.infDist (_root_.Jackson.restrictIcc hf.1.continuousOn)
        (_root_.polyLE (Set.Icc (-1 : ℝ) 1) n : Set C(Set.Icc (-1 : ℝ) 1, ℝ))
      ≤ (d : ℝ) * (1 + π ^ 2 / 2) ^ (k + 1) * (M : ℝ) / (n : ℝ) ^ ((k : ℝ) + (α : ℝ)) := by
  have hs : UniqueDiffOn ℝ (Set.Icc (-1 : ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
  refine _root_.Jackson.infDist_le_of_holder_poly
    (D := fun j => iteratedDerivWithin j f (Set.Icc (-1 : ℝ) 1)) ?_ ?_ ?_
    M.coe_nonneg α.coe_nonneg (by exact_mod_cast hα1) ?_ hkn hd
  · intro x
    rw [iteratedDerivWithin_zero]
    rfl
  · intro j hj
    exact hf.1.continuousOn_iteratedDerivWithin (by exact_mod_cast hj) hs
  · intro j hj x hx
    rw [iteratedDerivWithin_succ]
    exact (hf.1.differentiableOn_iteratedDerivWithin (m := j) (by exact_mod_cast hj) hs
      x hx).hasDerivWithinAt
  · intro u hu v hv
    have h := hf.2.dist_le hu hv
    rwa [Real.dist_eq, Real.dist_eq] at h

/-- **(3.7.11)**: combining the Lebesgue lemma for the Fourier projection with Jackson's theorem,
`‖f − 𝓕ₙf‖_∞ ≤ (1 + ‖𝓕ₙ‖) c^{k+1} Mₖ / n^{k+α}` for `f ∈ C_p^{k,α}(2π)`. -/
theorem equation_3_7_11 {k n : ℕ} {α M : ℝ≥0} (hα0 : 0 < α) (hα1 : α ≤ 1) (hn : 1 ≤ n)
    {g : ℝ → ℝ} (hg : HolderClass k α M g) :
    ‖PeriodicCont.ofIsPeriodicCont hg.1 - fourierProj n (PeriodicCont.ofIsPeriodicCont hg.1)‖
      ≤ (1 + ‖fourierProj n‖) *
        ((1 + π ^ 2 / 2) ^ (k + 1) * (M : ℝ) / (n : ℝ) ^ ((k : ℝ) + (α : ℝ))) := by
  have h := norm_sub_fourierProj_le n (PeriodicCont.ofIsPeriodicCont hg.1)
  rw [← norm_fourierProj] at h
  exact h.trans (mul_le_mul_of_nonneg_left (theorem_3_7_1 hα0 hα1 hn hg) (by positivity))

/-- **(3.7.12)**: the resulting rate `‖f − 𝓕ₙf‖_∞ ≤ c_k log n / n^{k+α}` for `n ≥ 2`, with `c_k`
depending linearly on the Hölder constant `Mₖ` and otherwise only on `k`. The constant is explicit
here because the growth `Lₙ ≤ 1 + log (2n + 1)` of the Lebesgue constants is. -/
theorem equation_3_7_12 (k : ℕ) {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ (M : ℝ≥0) (g : ℝ → ℝ) (hg : HolderClass k α M g) (n : ℕ), 2 ≤ n →
      ‖PeriodicCont.ofIsPeriodicCont hg.1 - fourierProj n (PeriodicCont.ofIsPeriodicCont hg.1)‖
        ≤ c * (M : ℝ) * Real.log n / (n : ℝ) ^ ((k : ℝ) + (α : ℝ)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  set c₀ : ℝ := 1 + (2 + Real.log 3) / Real.log 2 with hc₀
  have hc₀pos : 0 < c₀ := by
    rw [hc₀]
    positivity
  have hcpos : 0 < c₀ * (1 + π ^ 2 / 2) ^ (k + 1) := by
    refine mul_pos hc₀pos (pow_pos ?_ _)
    positivity
  refine ⟨c₀ * (1 + π ^ 2 / 2) ^ (k + 1), hcpos, fun M g hg n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hnR
  have hlognpos : 0 < Real.log n := lt_of_lt_of_le hlog2 hlogn
  -- the Lebesgue constants grow at most like `log n`
  have hleb : 1 + ‖fourierProj n‖ ≤ c₀ * Real.log n := by
    rw [norm_fourierProj]
    have h1 := lebesgueConstant_le n
    have h2 : Real.log (2 * (n : ℝ) + 1) ≤ Real.log 3 + Real.log n := by
      have h3 : (2 : ℝ) * (n : ℝ) + 1 ≤ 3 * (n : ℝ) := by linarith
      calc Real.log (2 * (n : ℝ) + 1) ≤ Real.log (3 * (n : ℝ)) :=
            Real.log_le_log (by linarith) h3
        _ = Real.log 3 + Real.log n := Real.log_mul (by norm_num) (by linarith)
    have h4 : (2 : ℝ) + Real.log 3 ≤ (2 + Real.log 3) / Real.log 2 * Real.log n := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
      nlinarith
    rw [hc₀]
    nlinarith
  -- Jackson's theorem
  have hjack := theorem_3_7_1 hα0 hα1 hn1 hg
  have hden : (0 : ℝ) < (n : ℝ) ^ ((k : ℝ) + (α : ℝ)) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hnum : (0 : ℝ) ≤ (1 + π ^ 2 / 2) ^ (k + 1) * (M : ℝ) := by positivity
  have h := norm_sub_fourierProj_le n (PeriodicCont.ofIsPeriodicCont hg.1)
  rw [← norm_fourierProj] at h
  calc ‖PeriodicCont.ofIsPeriodicCont hg.1 - fourierProj n (PeriodicCont.ofIsPeriodicCont hg.1)‖
      ≤ (1 + ‖fourierProj n‖) *
          Metric.infDist (PeriodicCont.ofIsPeriodicCont hg.1)
            (trigPolyLE (2 * π) n : Set C(AddCircle (2 * π), ℝ)) := h
    _ ≤ (c₀ * Real.log n) *
          ((1 + π ^ 2 / 2) ^ (k + 1) * (M : ℝ) / (n : ℝ) ^ ((k : ℝ) + (α : ℝ))) := by
        refine mul_le_mul hleb hjack (Metric.infDist_nonneg) (by positivity)
    _ = c₀ * (1 + π ^ 2 / 2) ^ (k + 1) * (M : ℝ) * Real.log n /
          (n : ℝ) ^ ((k : ℝ) + (α : ℝ)) := by
        field_simp

end JacksonTheorem

/-! ### (3.7.21)–(3.7.22): the convergence of trigonometric interpolation -/

section TrigonometricInterpolationRate

open Real NNReal _root_.PeriodicCont

/-- **(3.7.21)**: the Lebesgue lemma for the interpolatory projection `𝓘ₙ`, combined with
Jackson's theorem, gives `‖f − 𝓘ₙf‖_∞ ≤ (1 + ‖𝓘ₙ‖) c^{k+1} Mₖ / n^{k+α}` for
`f ∈ C_p^{k,α}(2π)`, with `c = 1 + π²/2`.

No bound on `‖𝓘ₙ‖` enters here: the statement is about the operator norm itself, exactly as the
book writes it. -/
theorem equation_3_7_21 {k n : ℕ} {α M : ℝ≥0} (hα0 : 0 < α) (hα1 : α ≤ 1) (hn : 1 ≤ n)
    {g : ℝ → ℝ} (hg : HolderClass k α M g) :
    ‖PeriodicCont.ofIsPeriodicCont hg.1
        - trigInterpCLM (2 * π) n (PeriodicCont.ofIsPeriodicCont hg.1)‖
      ≤ (1 + ‖trigInterpCLM (2 * π) n‖) *
        ((1 + π ^ 2 / 2) ^ (k + 1) * (M : ℝ) / (n : ℝ) ^ ((k : ℝ) + (α : ℝ))) :=
  (norm_sub_trigInterpCLM_le n _).trans
    (mul_le_mul_of_nonneg_left (theorem_3_7_1 hα0 hα1 hn hg) (by positivity))

/-- **(3.7.20) is false as printed.** [han2009theoretical] quote Rivlin for
`‖𝓘ₙ‖ ≤ 1 + (2/π) log n` when `n ≥ 1`. At `n = 1` its right-hand side is `1`, while the Lebesgue
function of interpolation at the three nodes `0, 2π/3, 4π/3` takes the value `5/3` at `π/3`
(`le_norm_trigInterpCLM_one`). Rivlin's `n` counts the interpolation *nodes*, which here number
`2 n + 1`; `norm_trigInterpCLM_bound` is the bound proved in its place. -/
theorem not_equation_3_7_20 :
    ¬ ∀ n : ℕ, 1 ≤ n → ‖trigInterpCLM (2 * π) n‖ ≤ 1 + 2 / π * Real.log n := by
  intro h
  have h1 := h 1 le_rfl
  rw [Nat.cast_one, Real.log_one, mul_zero, add_zero] at h1
  linarith [le_norm_trigInterpCLM_one]

/-- **(3.7.20)** in a form that holds: `‖𝓘ₙ‖ ≤ 2 + (2/π) log (2 n + 1)`, the backbone's
`norm_trigInterpCLM_le`. It keeps the coefficient `2/π` of the printed bound, which is sharp, and
so gives the same `𝓞(log n)` growth; the additive constant is `2` rather than `1`, one unit for
each of the two nodes nearest the evaluation point. The sharp statement,
`‖𝓘ₙ‖ ≤ 1 + (2/π) log (2 n + 1)`, is not proved: its two sides differ by about `0.04` for
every `n`. -/
theorem norm_trigInterpCLM_bound (n : ℕ) :
    ‖trigInterpCLM (2 * π) n‖ ≤ 2 + 2 / π * Real.log (2 * (n : ℝ) + 1) :=
  norm_trigInterpCLM_le n

/-- **(3.7.22)**: the rate `‖f − 𝓘ₙf‖_∞ ≤ c_k log n / n^{k+α}` for `n ≥ 2`, with `c_k` depending
linearly on the Hölder constant `Mₖ` and otherwise only on `k`. The constant is explicit here
because the growth `‖𝓘ₙ‖ ≤ 2 + (2/π) log (2n + 1)` of the interpolation projections is. -/
theorem equation_3_7_22 (k : ℕ) {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ (M : ℝ≥0) (g : ℝ → ℝ) (hg : HolderClass k α M g) (n : ℕ), 2 ≤ n →
      ‖PeriodicCont.ofIsPeriodicCont hg.1
          - trigInterpCLM (2 * π) n (PeriodicCont.ofIsPeriodicCont hg.1)‖
        ≤ c * (M : ℝ) * Real.log n / (n : ℝ) ^ ((k : ℝ) + (α : ℝ)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  set c₀ : ℝ := 1 + (3 + Real.log 3) / Real.log 2 with hc₀
  have hc₀pos : 0 < c₀ := by
    rw [hc₀]
    positivity
  have hcpos : 0 < c₀ * (1 + π ^ 2 / 2) ^ (k + 1) := by
    refine mul_pos hc₀pos (pow_pos ?_ _)
    positivity
  refine ⟨c₀ * (1 + π ^ 2 / 2) ^ (k + 1), hcpos, fun M g hg n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hnR
  have hlognpos : 0 < Real.log n := lt_of_lt_of_le hlog2 hlogn
  -- the norms of the interpolation projections grow at most like `log n`
  have hleb : 1 + ‖trigInterpCLM (2 * π) n‖ ≤ c₀ * Real.log n := by
    have h1 := norm_trigInterpCLM_le n
    have hlogNnn : 0 ≤ Real.log (2 * (n : ℝ) + 1) := Real.log_nonneg (by linarith)
    have hlogN : Real.log (2 * (n : ℝ) + 1) ≤ Real.log 3 + Real.log n := by
      calc Real.log (2 * (n : ℝ) + 1) ≤ Real.log (3 * (n : ℝ)) :=
            Real.log_le_log (by linarith) (by linarith)
        _ = Real.log 3 + Real.log n := Real.log_mul (by norm_num) (by linarith)
    have hpi2 : (2 : ℝ) / π ≤ 1 := by
      rw [div_le_one Real.pi_pos]
      exact Real.two_le_pi
    have h2 : 2 / π * Real.log (2 * (n : ℝ) + 1) ≤ Real.log 3 + Real.log n := by
      nlinarith
    have h4 : (3 : ℝ) + Real.log 3 ≤ (3 + Real.log 3) / Real.log 2 * Real.log n := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
      nlinarith
    rw [hc₀]
    nlinarith
  -- Jackson's theorem
  have hjack := theorem_3_7_1 hα0 hα1 hn1 hg
  have hden : (0 : ℝ) < (n : ℝ) ^ ((k : ℝ) + (α : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
  have hnum : (0 : ℝ) ≤ (1 + π ^ 2 / 2) ^ (k + 1) * (M : ℝ) := by positivity
  calc ‖PeriodicCont.ofIsPeriodicCont hg.1
          - trigInterpCLM (2 * π) n (PeriodicCont.ofIsPeriodicCont hg.1)‖
      ≤ (1 + ‖trigInterpCLM (2 * π) n‖) *
          Metric.infDist (PeriodicCont.ofIsPeriodicCont hg.1)
            (trigPolyLE (2 * π) n : Set C(AddCircle (2 * π), ℝ)) :=
        norm_sub_trigInterpCLM_le n _
    _ ≤ (c₀ * Real.log n) *
          ((1 + π ^ 2 / 2) ^ (k + 1) * (M : ℝ) / (n : ℝ) ^ ((k : ℝ) + (α : ℝ))) :=
        mul_le_mul hleb hjack Metric.infDist_nonneg (by positivity)
    _ = c₀ * (1 + π ^ 2 / 2) ^ (k + 1) * (M : ℝ) * Real.log n /
          (n : ℝ) ^ ((k : ℝ) + (α : ℝ)) := by
        field_simp

end TrigonometricInterpolationRate

/-! ### Theorem 3.7.3: the Christoffel–Darboux identity -/

section ChristoffelDarboux

open MeasureTheory OrthogonalPolynomial Polynomial

variable {μ : MeasureTheory.Measure ℝ}

/-- **Theorem 3.7.3** (Christoffel–Darboux identity). For `{pₙ}` the orthonormal family of a
weight `w ≥ 0` — the monic orthogonal polynomials of the measure, scaled to unit `L²(w)` norm —
and `x ≠ t`,

`∑_{n=0}^{N} pₙ(x) pₙ(t) = (p_{N+1}(x) p_N(t) − p_N(x) p_{N+1}(t)) / (a_N (x − t))`

with `a_N = A_{N+1} / A_N` the ratio of the leading coefficients. -/
theorem theorem_3_7_3 (hw : IsWeight μ) (N : ℕ) {x t : ℝ} (hxt : x ≠ t) :
    ∑ n ∈ Finset.range (N + 1),
        (orthonormalFamily μ n).eval x * (orthonormalFamily μ n).eval t
      = ((orthonormalFamily μ (N + 1)).eval x * (orthonormalFamily μ N).eval t
          - (orthonormalFamily μ N).eval x * (orthonormalFamily μ (N + 1)).eval t)
        / ((orthonormalFamily μ (N + 1)).leadingCoeff /
            (orthonormalFamily μ N).leadingCoeff * (x - t)) := by
  rw [← cdA_eq_leadingCoeff_div hw]
  exact Polynomial.christoffel_darboux_div (orthonormalFamily_one hw)
    (orthonormalFamily_recurrence hw) (cdC_mul_cdA hw) N (cdA_pos hw N).ne' hxt

/-- **Theorem 3.7.3**, the confluent case `x = t`:

`∑_{n=0}^{N} pₙ(t)² = (p'_{N+1}(t) p_N(t) − p'_N(t) p_{N+1}(t)) / a_N`. -/
theorem theorem_3_7_3_confluent (hw : IsWeight μ) (N : ℕ) (t : ℝ) :
    ∑ n ∈ Finset.range (N + 1), (orthonormalFamily μ n).eval t ^ 2
      = ((derivative (orthonormalFamily μ (N + 1))).eval t * (orthonormalFamily μ N).eval t
          - (derivative (orthonormalFamily μ N)).eval t *
            (orthonormalFamily μ (N + 1)).eval t)
        / ((orthonormalFamily μ (N + 1)).leadingCoeff /
            (orthonormalFamily μ N).leadingCoeff) := by
  rw [← cdA_eq_leadingCoeff_div hw]
  exact Polynomial.christoffel_darboux_confluent_div (orthonormalFamily_one hw)
    (orthonormalFamily_recurrence hw) (cdC_mul_cdA hw) N t (cdA_pos hw N).ne'

end ChristoffelDarboux

/-! ### (3.7.13)–(3.7.17) and Example 3.7.4: least-squares projections on `C[-1, 1]` -/

section LeastSquares

open MeasureTheory Real Approximation _root_.PeriodicCont

/-- `[-1, 1]` is not empty, so the norm formula (3.7.17) applies to operators on `C[-1, 1]`. -/
instance : Nonempty (Set.Icc (-1 : ℝ) 1) :=
  Set.nonempty_coe_sort.2 (Set.nonempty_Icc.2 (by norm_num))

variable {N : ℕ} (μ : Measure (Set.Icc (-1 : ℝ) 1)) [IsFiniteMeasure μ]
  (p : Fin (N + 1) → C(Set.Icc (-1 : ℝ) 1, ℝ))

/-- **(3.7.13)**: for an orthonormal system `p₀, …, p_N` in `L²_w(-1, 1)` of continuous functions,
the least-squares projection of `u ∈ C[-1, 1]` onto their span is `P_N u = ∑ₙ ξₙ pₙ` with
`ξₙ = (u, pₙ)_{0,w}`.

The weight is carried by the measure `μ`; [han2009theoretical] §3.7.1 takes it to be the
orthonormal polynomial family of a weight `w` on `(-1, 1)`, but nothing here uses more than
continuity. -/
theorem equation_3_7_13 (u : C(Set.Icc (-1 : ℝ) 1, ℝ)) :
    expansionCLM μ p u = ∑ n, (∫ t, u t * p n t ∂μ) • p n :=
  expansionCLM_eq_sum μ p u

/-- **(3.7.14)**, the Lebesgue lemma for the least-squares projection: `‖u − P_N u‖_∞ ≤
(1 + ‖P_N‖) ‖u − q‖_∞` for the best `q` in the span, provided the system is orthonormal. -/
theorem equation_3_7_14 (h : IsOrthonormal μ p) (u : C(Set.Icc (-1 : ℝ) 1, ℝ)) :
    ‖u - expansionCLM μ p u‖
      ≤ (1 + ‖expansionCLM μ p‖) *
          Metric.infDist u (Submodule.span ℝ (Set.range p) : Set C(Set.Icc (-1 : ℝ) 1, ℝ)) :=
  h.norm_sub_expansionCLM_le u

/-- **(3.7.15)–(3.7.16)**: the least-squares projection is the integral operator of the reproducing
kernel `K (x, t) = ∑ₙ pₙ(x) pₙ(t)` of the system. -/
theorem equation_3_7_15 (u : C(Set.Icc (-1 : ℝ) 1, ℝ)) (x : Set.Icc (-1 : ℝ) 1) :
    expansionCLM μ p u x = ∫ t, (∑ n, p n x * p n t) * u t ∂μ :=
  rfl

/-- **(3.7.17)**: the norm of the least-squares projection as an operator on `C[-1, 1]` is the
largest row integral of its kernel, `‖P_N‖ = max_x ∫ |K (x, t)| dt`. This is (2.2.8), the norm of an
integral operator with continuous kernel, applied to (3.7.15). -/
theorem equation_3_7_17 :
    ‖expansionCLM μ p‖ = ⨆ x, ∫ t, |∑ n, p n x * p n t| ∂μ :=
  norm_expansionCLM μ p

/-! #### Example 3.7.4: the Chebyshev least-squares projection -/

/-- **Example 3.7.4**: the operator norm of the Chebyshev least-squares projection on `C[-1, 1]` is
exactly the `N`-th Lebesgue constant of the Fourier projection.

This is the book's derivation: the change of variables `x = cos θ`, `t = cos φ` turns the kernel
into `(1/π)[D_N(θ − φ) + D_N(θ + φ)]` (`chebyshevKernel_cos`), the row integral into
`(1/π) ∫₀^π |D_N(θ − φ) + D_N(θ + φ)| dφ`, and that is largest at `θ = 0`, where it is
`(2/π) ∫₀^π |D_N| = L_N`. The book then quotes (3.7.10) for `L_N = (4/π²) log N + 𝓞(1)`; the sharp
asymptotics are not proved here, and `norm_chebyshevProj_asymptotics` records instead the two-sided
bound the backbone does prove. -/
theorem example_3_7_4 (N : ℕ) : ‖chebyshevProj N‖ = lebesgueConstant N :=
  norm_chebyshevProj N

/-- The Chebyshev least-squares projections grow like `log N` in the uniform norm: this is what
[han2009theoretical] draw from Example 3.7.4 and (3.7.10), here with the two-sided bound the
backbone proves in place of the sharp constant. In particular `‖P_N‖ → ∞`, so by
`exists_not_tendsto_of_not_bddAbove` some `u ∈ C[-1, 1]` has `P_N u ↛ u` uniformly. -/
theorem norm_chebyshevProj_asymptotics (N : ℕ) :
    4 / π ^ 2 * Real.log N ≤ ‖chebyshevProj N‖ ∧
      ‖chebyshevProj N‖ ≤ 1 + Real.log (2 * (N : ℝ) + 1) := by
  rw [example_3_7_4]
  exact ⟨log_le_lebesgueConstant N, lebesgueConstant_le N⟩

end LeastSquares

end AtkinsonHan.Chapter03
