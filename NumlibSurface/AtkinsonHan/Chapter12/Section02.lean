import Numlib.Analysis.Fourier.Truncation
import Numlib.Analysis.Sobolev.Periodic
import Numlib.Approximation.Interpolation
import Numlib.Approximation.Jackson
import Numlib.Approximation.PiecewiseLinearL2
import Numlib.Approximation.TrigonometricInterpolation
import Numlib.IntegralEquations.Basic
import NumlibSurface.AtkinsonHan.Chapter12.Section01

/-!
# Atkinson–Han §12.2: examples of the projection method

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §12.2.

The section applies the framework of §12.1 to four concrete trial spaces.  What has to be supplied
for each is the pair of facts that Theorem 12.1.2 asks for: that the projections are uniformly
bounded and converge pointwise to the identity, so that `‖K - P_n K‖ → 0` by Lemma 12.1.4, and an
approximation-theoretic bound on `‖u - P_n u‖`.

All four trial spaces of the section are formalized here.  For §12.2.1 the projections are
interpolation at the breakpoints of a partition of `[a, b]`, and both facts come from
`Numlib/Approximation/Interpolation` — `tendsto_piecewiseLinearInterpCLM` for the pointwise
convergence and `norm_sub_piecewiseLinearInterpCLM_le` for the `h² ‖u''‖ / 8` bound.  Nothing about
the mesh is assumed beyond `h_n → 0`; the book's uniform mesh `h = (b - a) / n` is the case
`x_j = a + j h`.

For §12.2.2 and §12.2.4 the projections onto the trigonometric polynomials of degree at most `n`
are *not* pointwise convergent on `C_p(2π)` — their norms grow like `log n` — so Lemma 12.1.4 is
unavailable and `‖K - P_n K‖ → 0` has to be proved directly.  What makes it true is the Hölder
condition (12.2.16) on the kernel: it makes `K u` Hölder continuous with constant `c ‖u‖`, so
Jackson's theorem bounds the best approximation error of `K u` by `c ‖u‖ (π²/2)^α n^{-α}` and the
Lebesgue lemma converts that into `‖(I - P_n) K u‖ ≤ (1 + ‖P_n‖) c ‖u‖ (π²/2)^α n^{-α}`.  The two
projections differ only in the bound on `‖P_n‖`: `norm_trigInterpCLM_le` for interpolation and
`PeriodicCont.lebesgueConstant_le` for the Fourier truncation.

## Main results

* `equation_12_2_5` — for piecewise linear collocation on a sequence of partitions of vanishing
  mesh, `‖K - P_n K‖ → 0`, the collocation equations are uniquely solvable for all large `n`, and
  `‖u - u_n‖_∞ ≤ c h_n² ‖u''‖_∞` for a `C²` solution, with a constant independent of `n`.
* `equation_12_2_17` — for trigonometric collocation with a kernel Hölder continuous of exponent
  `α` in its first variable uniformly in the second, `‖K - P_n K‖ ≤ c log n / n^α`, so the
  collocation equations are uniquely solvable for all large `n` and the error is proportional to
  `‖u - P_n u‖_∞`.
* `equation_12_2_27` — `‖P_n‖ = O(log n)` for the Fourier truncation read on `C_p(2π)`, together
  with the fact that the family is *not* uniformly bounded, and then the same complete convergence
  analysis in the uniform norm for the Fourier–Galerkin method.
* `equation_12_2_24` — the `L²` truncation error `‖u - P_n u‖_{L²} ≤ ‖u‖_{H^r} / n^r` of the
  Fourier series of a function of the periodic Sobolev class `H^r(0, 2π)`, and `equation_12_2_25`
  the resulting rate `‖u - u_n‖_{L²} ≤ |λ| M ‖u‖_{H^r} / n^r` of the Fourier–Galerkin method.
* `equation_12_2_19` — the piecewise linear Galerkin method.  The trial space and the projection
  onto it are `piecewiseLinearLp` and `piecewiseLinearProjCLM` of
  `Numlib/Approximation/PiecewiseLinearL2`, whose `norm_sub_piecewiseLinearProjCLM_le` and
  `IntegralOperator.norm_iccToLp_le` are the two inequalities of (12.2.18) and whose
  `tendsto_piecewiseLinearProjCLM` is the pointwise convergence on the whole of `L²`.
  The theorem itself is `‖K - P_n K‖ → 0`, unique solvability for large `n`, and
  `‖u - u_n‖_{L²} ≤ |λ| M √(b - a) h_n² ‖u''‖_∞ / 8` for a `C²` solution.

## Not formalized here

The error bound of §12.2.3 is **(12.2.19)** and not (12.2.24), which is in §12.2.4: an earlier
plan and the chapter audit both mis-numbered it, and stated it in the `L²` norm of `u''`, which
would have asked for an `L²` interpolation estimate.  The book's own bound goes through the
*uniform* norm of the interpolation error, so `norm_sub_piecewiseLinearInterpCLM_le` supplies all
of the approximation theory.

Compactness of the integral operator on `L²` is a *hypothesis* of `equation_12_2_25` rather than a
consequence: on `C[a, b]` it is `IntegralOperator.isCompactOperator_kernelCLM`, but on `L²` it is
the Hilbert–Schmidt theorem, and `IntegralOperator.l2KernelCLM` of
`Numlib/IntegralEquations/L2Kernel` bounds the operator and computes its adjoint without showing it
compact.  The book takes the same fact from its Chapter 2.  The same holds of `equation_12_2_19`.

Example 12.2.1 is a numerical table and is not stated.  Every number in it is measured — the nodal
errors of Table 12.1 and their ratios — and so are the two remarks made about them: that the
observed rate for `u = √x` beats the approximation error of the trial space, and that the ratio of
the nodal error to the uniform error tends to zero.  The bound the table illustrates is
`equation_12_2_5`, and the superconvergence at the nodes that the second remark points at is §12.3.

## Conventions

As in §12.1 the book's scalar `λ` is written `μ`, `λ` being Lean's lambda binder.  The book's
partition is indexed by its number of subintervals; here a sequence `y n : ℕ → Icc a b` of nodes
and a count `N n` are given, of which only `y n 0, …, y n (N n + 1)` are used, exactly as
`piecewiseLinearInterpCLM` takes them.

`C_p(2π)` is `C(ℝ/2πℤ, ℝ)`, and the integral operator on it is taken against the *normalized* Haar
measure `haarAddCircle`, whose total mass is one rather than the book's `2π`; the normalization
rescales the kernel and changes nothing in the statements below, all of which quantify over an
arbitrary constant.  The Hölder condition (12.2.16) is stated on representatives, that is for
`x, ξ` ranging over `ℝ`, which is how the book writes it.  `L²(0, 2π)` is likewise
`Lp ℝ 2 haarAddCircle`, whose measure is normalized; the book's `H^r` norm is the weighted `ℓ²` norm
of the Fourier coefficients, `periodicSobolevWeight` of `Numlib/Analysis/Sobolev/Periodic`, and is
written here as a `HasSum` hypothesis on the coefficients rather than through the space
`PeriodicSobolev r`, which is complex and carries no map to `Lp ℝ 2 haarAddCircle`.
-/

open Filter Topology

open scoped ContDiff

namespace AtkinsonHan.Chapter12

/-! ### Piecewise linear collocation -/

/-- **(12.2.5), the piecewise linear collocation method.**  Let `K` be the Fredholm operator of a
continuous kernel on `[a, b]`, let `λ ≠ 0` be such that `λ - K` is invertible, and let `P_n` be
interpolation at the breakpoints of a sequence of partitions of `[a, b]` whose mesh `h_n` tends to
zero.  Then:

* `‖K - P_n K‖ → 0`, which is hypothesis (12.1.21);
* for all large `n` the collocation equations `P_n ((λ - K) u_n) = P_n f` have a unique solution for
  every right-hand side;
* and if the exact solution `u` is `C²` with `|u''| ≤ M` on `[a, b]`, then
  `‖u - u_n‖_∞ ≤ c h_n² M` with `c = |λ| ‖(λ - K)⁻¹‖ / 4` independent of `n`.

The three ingredients are Lemma 12.1.4 (applied to the compact operator `K`, which is
`IntegralOperator.isCompactOperator_fredholm`), Theorem 12.1.2, and (12.1.24) combined with the
interpolation error bound `‖u - P_n u‖ ≤ h_n² M / 8`. -/
theorem equation_12_2_5 {a b : ℝ} (hab : a ≤ b) {μ : ℝ} (hμ : μ ≠ 0)
    (k : C(Set.Icc a b × Set.Icc a b, ℝ)) {N : ℕ → ℕ} {y : ℕ → ℕ → Set.Icc a b} {h : ℕ → ℝ}
    (hstep : ∀ n, ∀ i ≤ N n, (y n i : ℝ) < (y n (i + 1) : ℝ))
    (hfirst : ∀ n, (y n 0 : ℝ) = a) (hlast : ∀ n, (y n (N n + 1) : ℝ) = b)
    (hmesh : ∀ n, ∀ i ≤ N n, (y n (i + 1) : ℝ) - (y n i : ℝ) ≤ h n)
    (hh : Tendsto h atTop (𝓝 0)) {e : C(Set.Icc a b, ℝ) ≃L[ℝ] C(Set.Icc a b, ℝ)}
    (he : (e : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))
      = μ • 1 - IntegralOperator.fredholm hab k) :
    Tendsto (fun n => ‖IntegralOperator.fredholm hab k -
        piecewiseLinearInterpCLM (N n) (y n) ∘L IntegralOperator.fredholm hab k‖) atTop (𝓝 0) ∧
      ∃ c : ℝ, ∀ᶠ n in atTop,
        (∀ f : C(Set.Icc a b, ℝ), ∃! un : C(Set.Icc a b, ℝ),
          IsProjectionSolution μ (IntegralOperator.fredholm hab k)
            (piecewiseLinearInterpCLM (N n) (y n)) f un) ∧
        ∀ (g : ℝ → ℝ) (M : ℝ) (f u un : C(Set.Icc a b, ℝ)),
          ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) g → (∀ t : Set.Icc a b, u t = g (t : ℝ)) →
          (∀ t ∈ Set.Icc a b, |iteratedDeriv 2 g t| ≤ M) →
          (μ • 1 - IntegralOperator.fredholm hab k :
            C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) u = f →
          IsProjectionSolution μ (IntegralOperator.fredholm hab k)
            (piecewiseLinearInterpCLM (N n) (y n)) f un →
          ‖u - un‖ ≤ c * h n ^ 2 * M := by
  set K : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ) := IntegralOperator.fredholm hab k with hK
  set A : ℝ := ‖(e.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖ with hA
  have hA0 : 0 ≤ A := norm_nonneg _
  have hcpt : IsCompactOperator K := IntegralOperator.isCompactOperator_fredholm hab k
  have hP : ∀ u : C(Set.Icc a b, ℝ),
      Tendsto (fun n => piecewiseLinearInterpCLM (N n) (y n) u) atTop (𝓝 u) :=
    tendsto_piecewiseLinearInterpCLM hstep hfirst hlast hmesh hh
  have hconv : Tendsto (fun n => ‖K - piecewiseLinearInterpCLM (N n) (y n) ∘L K‖) atTop (𝓝 0) :=
    lemma_12_1_4 hcpt hP
  refine ⟨hconv, ⟨‖μ‖ * A / 4, ?_⟩⟩
  have hsmall : ∀ᶠ n in atTop, A * ‖K - piecewiseLinearInterpCLM (N n) (y n) ∘L K‖ < 1 / 2 := by
    have h0 : Tendsto (fun n => A * ‖K - piecewiseLinearInterpCLM (N n) (y n) ∘L K‖) atTop
        (𝓝 0) := by simpa using hconv.const_mul A
    exact h0.eventually (eventually_lt_nhds (by norm_num))
  filter_upwards [hsmall] with n hn
  have hidem : IsIdempotentElem (piecewiseLinearInterpCLM (N n) (y n)) :=
    isIdempotentElem_piecewiseLinearInterpCLM (hstep n) (hfirst n) (hlast n)
  obtain ⟨e', he'coe, he'norm, huniq⟩ := theorem_12_1_2 hμ hidem e he (by rw [← hA]; linarith)
  have hb1 : ‖(e'.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖ ≤ 2 * A := by
    refine he'norm.trans ?_
    rw [← hA, div_le_iff₀ (by linarith)]
    nlinarith [norm_nonneg (K - piecewiseLinearInterpCLM (N n) (y n) ∘L K)]
  refine ⟨huniq, fun g M f u un hg hu hM hueq hun => ?_⟩
  have hb2 : ‖u - piecewiseLinearInterpCLM (N n) (y n) u‖ ≤ h n ^ 2 / 8 * M :=
    norm_sub_piecewiseLinearInterpCLM_le (hstep n) (hfirst n) (hlast n) hg hu (hmesh n) hM
  have hkey := (equation_12_1_24 hidem he'coe hueq hun).2
  calc ‖u - un‖
      ≤ ‖μ‖ * ‖(e'.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖ *
          ‖u - piecewiseLinearInterpCLM (N n) (y n) u‖ := hkey
    _ ≤ ‖μ‖ * (2 * A) * (h n ^ 2 / 8 * M) := by gcongr
    _ = ‖μ‖ * A / 4 * h n ^ 2 * M := by ring

/-! ### Projection methods on the circle in the uniform norm -/

section Periodic

open AddCircle IntegralOperator MeasureTheory PeriodicCont

open scoped Real

local notation "Cₚ" => C(AddCircle (2 * Real.pi), ℝ)

/-- **The Hölder condition (12.2.16) makes every image `K u` Hölder continuous** with constant
`c ‖u‖`: the hypothesis is uniform in the integration variable, so it survives the integration. -/
private theorem holder_kernelCLM_apply {α c : ℝ} (hc : 0 ≤ c)
    {k : C(AddCircle (2 * Real.pi) × AddCircle (2 * Real.pi), ℝ)}
    (hk : ∀ (s t : ℝ) (y : AddCircle (2 * Real.pi)), |k (↑s, y) - k (↑t, y)| ≤ c * |s - t| ^ α)
    (u : Cₚ) (s t : ℝ) :
    |Jackson.lift (kernelCLM haarAddCircle k u) s - Jackson.lift (kernelCLM haarAddCircle k u) t|
      ≤ c * ‖u‖ * |s - t| ^ α := by
  have hs : Integrable (fun y => k ((s : AddCircle (2 * Real.pi)), y) * u y) haarAddCircle :=
    integrable_kernel_mul haarAddCircle k u _
  have ht : Integrable (fun y => k ((t : AddCircle (2 * Real.pi)), y) * u y) haarAddCircle :=
    integrable_kernel_mul haarAddCircle k u _
  have hb : ∀ y : AddCircle (2 * Real.pi),
      |k ((s : AddCircle (2 * Real.pi)), y) * u y - k ((t : AddCircle (2 * Real.pi)), y) * u y|
        ≤ c * |s - t| ^ α * ‖u‖ := by
    intro y
    have hu : |u y| ≤ ‖u‖ := by simpa [Real.norm_eq_abs] using u.norm_coe_le_norm y
    rw [← sub_mul, abs_mul]
    exact mul_le_mul (hk s t y) hu (abs_nonneg _) (by positivity)
  simp only [Jackson.lift, kernelCLM_apply]
  rw [← integral_sub hs ht]
  calc |∫ y, (k ((s : AddCircle (2 * Real.pi)), y) * u y
        - k ((t : AddCircle (2 * Real.pi)), y) * u y) ∂haarAddCircle|
      ≤ ∫ y, |k ((s : AddCircle (2 * Real.pi)), y) * u y
          - k ((t : AddCircle (2 * Real.pi)), y) * u y| ∂haarAddCircle :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _y : AddCircle (2 * Real.pi), c * |s - t| ^ α * ‖u‖ ∂haarAddCircle :=
        integral_mono (hs.sub ht).abs (integrable_const _) hb
    _ = c * ‖u‖ * |s - t| ^ α := by
        rw [integral_const, probReal_univ, one_smul]
        ring

/-- **The projection error of a Hölder kernel operator**, the heart of both (12.2.17) and the
uniform analysis of §12.2.4.  If `P` reproduces the trigonometric polynomials of degree at most `n`
well enough to satisfy the Lebesgue lemma with constant `L`, then

`‖K - P K‖ ≤ L c (π²/2)^α n^{-α}`.

Jackson's theorem supplies the best approximation error of `K u`, which
`holder_kernelCLM_apply` has just shown to be Hölder of constant `c ‖u‖`. -/
private theorem norm_sub_comp_kernelCLM_le {α c : ℝ} (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    {k : C(AddCircle (2 * Real.pi) × AddCircle (2 * Real.pi), ℝ)}
    (hk : ∀ (s t : ℝ) (y : AddCircle (2 * Real.pi)), |k (↑s, y) - k (↑t, y)| ≤ c * |s - t| ^ α)
    {n : ℕ} (hn : 1 ≤ n) {P : Cₚ →L[ℝ] Cₚ} {L : ℝ} (hL : 0 ≤ L)
    (hPL : ∀ f : Cₚ, ‖f - P f‖ ≤ L * Metric.infDist f (trigPolyLE (2 * Real.pi) n : Set Cₚ)) :
    ‖kernelCLM haarAddCircle k - P ∘L kernelCLM haarAddCircle k‖
      ≤ L * (c * (Real.pi ^ 2 / 2) ^ α) / (n : ℝ) ^ α := by
  have hpi := Real.pi_pos
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hrpow : (0 : ℝ) ≤ (Real.pi ^ 2 / 2) ^ α := Real.rpow_nonneg (by positivity) α
  have hnpos : (0 : ℝ) < (n : ℝ) ^ α := Real.rpow_pos_of_pos (by linarith) α
  refine ContinuousLinearMap.opNorm_le_bound _
    (div_nonneg (mul_nonneg hL (mul_nonneg hc hrpow)) hnpos.le) fun u => ?_
  have hbound : Metric.infDist (kernelCLM haarAddCircle k u) (trigPolyLE (2 * Real.pi) n : Set Cₚ)
      ≤ c * ‖u‖ * ((Real.pi ^ 2 / 2) ^ α / (n : ℝ) ^ α) := by
    refine (Jackson.infDist_le_of_holder (by positivity) hα0 hα1
      (holder_kernelCLM_apply hc hk u) n).trans ?_
    have h1 : Real.pi * Real.sin (Jackson.angle n / 2) ≤ Real.pi ^ 2 / 2 / (n : ℝ) := by
      refine (Jackson.pi_mul_sin_half_angle_le n).trans ?_
      rw [div_le_div_iff₀ (by positivity) (by linarith)]
      nlinarith
    have h2 : (Real.pi * Real.sin (Jackson.angle n / 2)) ^ α
        ≤ (Real.pi ^ 2 / 2 / (n : ℝ)) ^ α :=
      Real.rpow_le_rpow (mul_pos hpi (Jackson.sin_half_angle_pos n)).le h1 hα0
    calc c * ‖u‖ * (Real.pi * Real.sin (Jackson.angle n / 2)) ^ α
        ≤ c * ‖u‖ * (Real.pi ^ 2 / 2 / (n : ℝ)) ^ α :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = c * ‖u‖ * ((Real.pi ^ 2 / 2) ^ α / (n : ℝ) ^ α) := by
          rw [Real.div_rpow (by positivity) (Nat.cast_nonneg n)]
  have happ : (kernelCLM haarAddCircle k - P ∘L kernelCLM haarAddCircle k) u
      = kernelCLM haarAddCircle k u - P (kernelCLM haarAddCircle k u) := rfl
  rw [happ]
  calc ‖kernelCLM haarAddCircle k u - P (kernelCLM haarAddCircle k u)‖
      ≤ L * Metric.infDist (kernelCLM haarAddCircle k u)
          (trigPolyLE (2 * Real.pi) n : Set Cₚ) := hPL _
    _ ≤ L * (c * ‖u‖ * ((Real.pi ^ 2 / 2) ^ α / (n : ℝ) ^ α)) := by gcongr
    _ = L * (c * (Real.pi ^ 2 / 2) ^ α) / (n : ℝ) ^ α * ‖u‖ := by
        field_simp

/-- `A + B log (2 n + 1) ≤ c log n` for `n ≥ 2`, the step that turns the two Lebesgue constant
bounds into a clean `𝓞(log n)`. -/
private theorem add_mul_log_le {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) {n : ℕ} (hn : 2 ≤ n) :
    A + B * Real.log (2 * (n : ℝ) + 1)
      ≤ (A / Real.log 2 + B * (Real.log 3 / Real.log 2 + 1)) * Real.log n := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hnR
  have h2 : Real.log (2 * (n : ℝ) + 1) ≤ Real.log 3 + Real.log n := by
    calc Real.log (2 * (n : ℝ) + 1) ≤ Real.log (3 * (n : ℝ)) :=
          Real.log_le_log (by linarith) (by linarith)
      _ = Real.log 3 + Real.log n := Real.log_mul (by norm_num) (by linarith)
  have hA' : A ≤ A / Real.log 2 * Real.log n := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    exact mul_le_mul_of_nonneg_left hlogn hA
  have hratio : (1 : ℝ) ≤ Real.log n / Real.log 2 := (le_div_iff₀ hlog2).2 (by linarith)
  have hB' : B * Real.log 3 ≤ B * (Real.log 3 / Real.log 2) * Real.log n := by
    have hrw : B * (Real.log 3 / Real.log 2) * Real.log n
        = B * Real.log 3 * (Real.log n / Real.log 2) := by
      field_simp
    rw [hrw]
    nlinarith [mul_nonneg hB hlog3]
  have hBlog : B * Real.log (2 * (n : ℝ) + 1) ≤ B * Real.log 3 + B * Real.log n := by
    nlinarith [mul_le_mul_of_nonneg_left h2 hB]
  nlinarith

/-- `log n / n^α → 0` for a positive exponent, along the naturals. -/
private theorem tendsto_log_div_rpow {α : ℝ} (hα : 0 < α) :
    Tendsto (fun n : ℕ => Real.log n / (n : ℝ) ^ α) atTop (𝓝 0) :=
  ((isLittleO_log_rpow_atTop hα).tendsto_div_nhds_zero).comp tendsto_natCast_atTop_atTop

/-- The projection equations are uniquely solvable for all large `n` as soon as the projection
error `‖K - P_n K‖` tends to zero; this is Theorem 12.1.2 read along the filter. -/
private theorem eventually_existsUnique_projectionSolution {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] {μ : ℝ} (hμ : μ ≠ 0) {K : X →L[ℝ] X} {P : ℕ → X →L[ℝ] X}
    (hP : ∀ n, IsIdempotentElem (P n)) {e : X ≃L[ℝ] X} (he : (e : X →L[ℝ] X) = μ • 1 - K)
    (hconv : Tendsto (fun n => ‖K - P n ∘L K‖) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, ∀ f : X, ∃! un : X, IsProjectionSolution μ K (P n) f un := by
  have hsmall : ∀ᶠ n in atTop, ‖(e.symm : X →L[ℝ] X)‖ * ‖K - P n ∘L K‖ < 1 := by
    have h0 : Tendsto (fun n => ‖(e.symm : X →L[ℝ] X)‖ * ‖K - P n ∘L K‖) atTop (𝓝 0) := by
      simpa using hconv.const_mul ‖(e.symm : X →L[ℝ] X)‖
    exact h0.eventually (eventually_lt_nhds (by norm_num))
  filter_upwards [hsmall] with n hn
  obtain ⟨-, -, -, huniq⟩ := theorem_12_1_2 hμ (hP n) e he hn
  exact huniq

/-- **(12.2.17), trigonometric collocation.**  Let `K` be the integral operator on `C_p(2π)` of a
continuous kernel satisfying the Hölder condition (12.2.16),

`|k (x, y) - k (ξ, y)| ≤ c |x - ξ|^α`  for all `x, ξ, y`,

with `0 < α ≤ 1`, let `λ ≠ 0` be such that `λ - K` is invertible, and let `P_n` be interpolation at
the `2 n + 1` equidistant nodes.  Then:

* `‖K - P_n K‖ ≤ c' log n / n^α` for `n ≥ 2` — this is (12.2.17) — and hence `‖K - P_n K‖ → 0`,
  which is the hypothesis (12.1.21) of Theorem 12.1.2;
* for all large `n` the collocation equations `P_n ((λ - K) u_n) = P_n f` are uniquely solvable for
  every right-hand side, and `‖u - u_n‖_∞ ≤ |λ| (1 + γ_n) ‖(λ - K)⁻¹‖ ‖u - P_n u‖_∞` with
  `γ_n → 0`.

Lemma 12.1.4 is *not* the route: the Lebesgue constants of trigonometric interpolation grow like
`log n`, so `P_n u → u` fails for a general continuous `u`.  The estimate is proved directly, from
Jackson's theorem for the Hölder function `K u` and the Rivlin bound `norm_trigInterpCLM_le` on the
Lebesgue constants.  The second clause is Theorem 12.1.2 together with Exercise 12.1.3.

The book's two-sided (12.1.24) makes the converse of the error bound true as well, so
`‖u - u_n‖_∞ → 0` if and only if `‖u - P_n u‖_∞ → 0`, as the book observes. -/
theorem equation_12_2_17 {α c : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hc : 0 ≤ c)
    {k : C(AddCircle (2 * Real.pi) × AddCircle (2 * Real.pi), ℝ)}
    (hk : ∀ (s t : ℝ) (y : AddCircle (2 * Real.pi)), |k (↑s, y) - k (↑t, y)| ≤ c * |s - t| ^ α)
    {μ : ℝ} (hμ : μ ≠ 0) {e : Cₚ ≃L[ℝ] Cₚ}
    (he : (e : Cₚ →L[ℝ] Cₚ) = μ • 1 - kernelCLM haarAddCircle k) :
    (∃ c' : ℝ, 0 < c' ∧ ∀ n : ℕ, 2 ≤ n →
        ‖kernelCLM haarAddCircle k
            - trigInterpCLM (2 * Real.pi) n ∘L kernelCLM haarAddCircle k‖
          ≤ c' * Real.log n / (n : ℝ) ^ α) ∧
      Tendsto (fun n => ‖kernelCLM haarAddCircle k
        - trigInterpCLM (2 * Real.pi) n ∘L kernelCLM haarAddCircle k‖) atTop (𝓝 0) ∧
      ∃ γ : ℕ → ℝ, Tendsto γ atTop (𝓝 0) ∧ ∀ᶠ n in atTop,
        (∀ f : Cₚ, ∃! un : Cₚ, IsProjectionSolution μ (kernelCLM haarAddCircle k)
          (trigInterpCLM (2 * Real.pi) n) f un) ∧
        ∀ f u un : Cₚ, (μ • 1 - kernelCLM haarAddCircle k : Cₚ →L[ℝ] Cₚ) u = f →
          IsProjectionSolution μ (kernelCLM haarAddCircle k)
            (trigInterpCLM (2 * Real.pi) n) f un →
          ‖u - un‖ ≤ ‖μ‖ * (1 + γ n) * ‖(e.symm : Cₚ →L[ℝ] Cₚ)‖ *
            ‖u - trigInterpCLM (2 * Real.pi) n u‖ := by
  have hpi := Real.pi_pos
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hrpow : (0 : ℝ) ≤ (Real.pi ^ 2 / 2) ^ α := Real.rpow_nonneg (by positivity) α
  set c₀ : ℝ := 3 / Real.log 2 + 2 / Real.pi * (Real.log 3 / Real.log 2 + 1) with hc₀
  have hc₀0 : 0 < c₀ := by
    rw [hc₀]
    have : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    positivity
  set c' : ℝ := c₀ * (c * (Real.pi ^ 2 / 2) ^ α) + 1 with hc'
  have hc'0 : 0 < c' := by
    rw [hc']
    nlinarith [mul_nonneg hc₀0.le (mul_nonneg hc hrpow)]
  have hmain : ∀ n : ℕ, 2 ≤ n →
      ‖kernelCLM haarAddCircle k
          - trigInterpCLM (2 * Real.pi) n ∘L kernelCLM haarAddCircle k‖
        ≤ c' * Real.log n / (n : ℝ) ^ α := by
    intro n hn
    have hn1 : 1 ≤ n := by omega
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlogn : (0 : ℝ) ≤ Real.log n := Real.log_nonneg (by linarith)
    have hnpos : (0 : ℝ) < (n : ℝ) ^ α := Real.rpow_pos_of_pos (by linarith) α
    have hLnn : (0 : ℝ) ≤ 1 + ‖trigInterpCLM (2 * Real.pi) n‖ := by positivity
    have hLle : 1 + ‖trigInterpCLM (2 * Real.pi) n‖ ≤ c₀ * Real.log n := by
      refine le_trans ?_ (add_mul_log_le (A := 3) (B := 2 / Real.pi) (by norm_num)
        (by positivity) hn)
      have := norm_trigInterpCLM_le (n := n)
      linarith
    have hstep := norm_sub_comp_kernelCLM_le hc hα0.le hα1 hk hn1 hLnn
      (fun f => norm_sub_trigInterpCLM_le n f)
    refine hstep.trans ?_
    rw [div_le_div_iff₀ hnpos hnpos]
    have hkey : (1 + ‖trigInterpCLM (2 * Real.pi) n‖) * (c * (Real.pi ^ 2 / 2) ^ α)
        ≤ c₀ * Real.log n * (c * (Real.pi ^ 2 / 2) ^ α) :=
      mul_le_mul_of_nonneg_right hLle (mul_nonneg hc hrpow)
    have hextra : (0 : ℝ) ≤ Real.log n * (n : ℝ) ^ α := by positivity
    rw [hc']
    nlinarith
  have htend : Tendsto (fun n => ‖kernelCLM haarAddCircle k
      - trigInterpCLM (2 * Real.pi) n ∘L kernelCLM haarAddCircle k‖) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _)
      (Eventually.mono (eventually_ge_atTop 2) hmain) ?_
    have h := (tendsto_log_div_rpow hα0).const_mul c'
    rw [mul_zero] at h
    exact h.congr fun n => (mul_div_assoc c' (Real.log n) ((n : ℝ) ^ α)).symm
  obtain ⟨γ, hγ, hev⟩ := exercise_12_1_3 (μ := μ) (K := kernelCLM haarAddCircle k)
    (P := fun n => trigInterpCLM (2 * Real.pi) n) (fun _ => isIdempotentElem_trigInterpCLM) he
    htend
  refine ⟨⟨c', hc'0, hmain⟩, htend, γ, hγ, ?_⟩
  filter_upwards [hev, eventually_existsUnique_projectionSolution hμ
    (P := fun n => trigInterpCLM (2 * Real.pi) n) (fun _ => isIdempotentElem_trigInterpCLM) he
    htend] with n h1 h2
  exact ⟨h2, h1⟩

/-- **(12.2.27) and the uniform convergence paragraph of §12.2.4.**  Read on the continuous
periodic functions rather than on `L²`, the Fourier truncation `P_n` is a projection whose norm is
the `n`-th Lebesgue constant, so

`‖P_n‖ ≤ 1 + log (2 n + 1)`,

which is (12.2.27); and the family is genuinely unbounded, so Lemma 12.1.4 cannot be applied.
Nevertheless, for a kernel satisfying the Hölder condition `|k (x, y) - k (ξ, y)| ≤ c |x - ξ|^α`
the same argument as for trigonometric collocation gives `‖K - P_n K‖ ≤ c' log n / n^α`, hence
`‖K - P_n K‖ → 0`, and Theorem 12.1.2 yields a complete convergence analysis in the uniform norm:
for all large `n` the Galerkin equations are uniquely solvable and
`‖u - u_n‖_∞ ≤ |λ| (1 + γ_n) ‖(λ - K)⁻¹‖ ‖u - P_n u‖_∞` with `γ_n → 0`.

The unboundedness is the lower bound `(4/π²) log n ≤ L_n` of `PeriodicCont.log_le_lebesgueConstant`
(the book's (3.7.10)), and the upper bound is `PeriodicCont.lebesgueConstant_le`. -/
theorem equation_12_2_27 {α c : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hc : 0 ≤ c)
    {k : C(AddCircle (2 * Real.pi) × AddCircle (2 * Real.pi), ℝ)}
    (hk : ∀ (s t : ℝ) (y : AddCircle (2 * Real.pi)), |k (↑s, y) - k (↑t, y)| ≤ c * |s - t| ^ α)
    {μ : ℝ} (hμ : μ ≠ 0) {e : Cₚ ≃L[ℝ] Cₚ}
    (he : (e : Cₚ →L[ℝ] Cₚ) = μ • 1 - kernelCLM haarAddCircle k) :
    (∀ n : ℕ, ‖fourierProj n‖ ≤ 1 + Real.log (2 * (n : ℝ) + 1)) ∧
      ¬ BddAbove (Set.range fun n : ℕ => ‖fourierProj n‖) ∧
      (∃ c' : ℝ, 0 < c' ∧ ∀ n : ℕ, 2 ≤ n →
        ‖kernelCLM haarAddCircle k - fourierProj n ∘L kernelCLM haarAddCircle k‖
          ≤ c' * Real.log n / (n : ℝ) ^ α) ∧
      Tendsto (fun n => ‖kernelCLM haarAddCircle k
        - fourierProj n ∘L kernelCLM haarAddCircle k‖) atTop (𝓝 0) ∧
      ∃ γ : ℕ → ℝ, Tendsto γ atTop (𝓝 0) ∧ ∀ᶠ n in atTop,
        (∀ f : Cₚ, ∃! un : Cₚ,
          IsProjectionSolution μ (kernelCLM haarAddCircle k) (fourierProj n) f un) ∧
        ∀ f u un : Cₚ, (μ • 1 - kernelCLM haarAddCircle k : Cₚ →L[ℝ] Cₚ) u = f →
          IsProjectionSolution μ (kernelCLM haarAddCircle k) (fourierProj n) f un →
          ‖u - un‖ ≤ ‖μ‖ * (1 + γ n) * ‖(e.symm : Cₚ →L[ℝ] Cₚ)‖ * ‖u - fourierProj n u‖ := by
  have hpi := Real.pi_pos
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hrpow : (0 : ℝ) ≤ (Real.pi ^ 2 / 2) ^ α := Real.rpow_nonneg (by positivity) α
  -- (12.2.27) itself, and the unboundedness that makes Lemma 12.1.4 unavailable
  have hnorm : ∀ n : ℕ, ‖fourierProj n‖ ≤ 1 + Real.log (2 * (n : ℝ) + 1) := fun n => by
    rw [norm_fourierProj]
    exact lebesgueConstant_le n
  have hunbdd : ¬ BddAbove (Set.range fun n : ℕ => ‖fourierProj n‖) := by
    rintro ⟨C, hC⟩
    have hlog : Tendsto (fun n : ℕ => 4 / Real.pi ^ 2 * Real.log n) atTop atTop :=
      Tendsto.const_mul_atTop (by positivity)
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    obtain ⟨n, hn⟩ := (hlog.eventually_gt_atTop C).exists
    have hle : 4 / Real.pi ^ 2 * Real.log n ≤ ‖fourierProj n‖ := by
      rw [norm_fourierProj]
      exact log_le_lebesgueConstant n
    exact absurd (hC ⟨n, rfl⟩) (not_le.2 (lt_of_lt_of_le hn hle))
  set c₀ : ℝ := 2 / Real.log 2 + (Real.log 3 / Real.log 2 + 1) with hc₀
  have hc₀0 : 0 < c₀ := by
    rw [hc₀]
    have : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    positivity
  set c' : ℝ := c₀ * (c * (Real.pi ^ 2 / 2) ^ α) + 1 with hc'
  have hc'0 : 0 < c' := by
    rw [hc']
    nlinarith [mul_nonneg hc₀0.le (mul_nonneg hc hrpow)]
  have hmain : ∀ n : ℕ, 2 ≤ n →
      ‖kernelCLM haarAddCircle k - fourierProj n ∘L kernelCLM haarAddCircle k‖
        ≤ c' * Real.log n / (n : ℝ) ^ α := by
    intro n hn
    have hn1 : 1 ≤ n := by omega
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlogn : (0 : ℝ) ≤ Real.log n := Real.log_nonneg (by linarith)
    have hnpos : (0 : ℝ) < (n : ℝ) ^ α := Real.rpow_pos_of_pos (by linarith) α
    have hLnn : (0 : ℝ) ≤ 1 + lebesgueConstant n := by
      rw [← norm_fourierProj n]
      positivity
    have hLle : 1 + lebesgueConstant n ≤ c₀ * Real.log n := by
      have h := add_mul_log_le (A := 2) (B := 1) (by norm_num) (by norm_num) hn
      have h2 := lebesgueConstant_le n
      rw [hc₀]
      linarith
    have hstep := norm_sub_comp_kernelCLM_le hc hα0.le hα1 hk hn1 hLnn
      (fun f => norm_sub_fourierProj_le n f)
    refine hstep.trans ?_
    rw [div_le_div_iff₀ hnpos hnpos]
    have hkey : (1 + lebesgueConstant n) * (c * (Real.pi ^ 2 / 2) ^ α)
        ≤ c₀ * Real.log n * (c * (Real.pi ^ 2 / 2) ^ α) :=
      mul_le_mul_of_nonneg_right hLle (mul_nonneg hc hrpow)
    have hextra : (0 : ℝ) ≤ Real.log n * (n : ℝ) ^ α := by positivity
    rw [hc']
    nlinarith
  have htend : Tendsto (fun n => ‖kernelCLM haarAddCircle k
      - fourierProj n ∘L kernelCLM haarAddCircle k‖) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _)
      (Eventually.mono (eventually_ge_atTop 2) hmain) ?_
    have h := (tendsto_log_div_rpow hα0).const_mul c'
    rw [mul_zero] at h
    exact h.congr fun n => (mul_div_assoc c' (Real.log n) ((n : ℝ) ^ α)).symm
  obtain ⟨γ, hγ, hev⟩ := exercise_12_1_3 (μ := μ) (K := kernelCLM haarAddCircle k)
    (P := fun n => fourierProj n) (fun n => isIdempotentElem_fourierProj n) he htend
  refine ⟨hnorm, hunbdd, ⟨c', hc'0, hmain⟩, htend, γ, hγ, ?_⟩
  filter_upwards [hev, eventually_existsUnique_projectionSolution hμ
    (P := fun n => fourierProj n) (fun n => isIdempotentElem_fourierProj n) he htend] with n h1 h2
  exact ⟨h2, h1⟩

end Periodic

/-! ### The Fourier–Galerkin method in `L²` -/

section Fourier

open AddCircle MeasureTheory

open scoped Real

local notation "L²p" => Lp ℝ 2 (haarAddCircle (T := 2 * Real.pi))

/-- **(12.2.24), the `L²` truncation error of a Fourier series in the periodic Sobolev scale.**
If the Fourier coefficients of `u ∈ L²(0, 2π)` satisfy

`‖u‖²_{H^r} = |c₀|² + ∑_{m ≠ 0} |m|^{2r} |c_m|² = S²`,

that is, if `u ∈ H^r(0, 2π)` with `‖u‖_{H^r} = S`, then the Fourier truncation `P_n` of degree `n`
satisfies

`‖u - P_n u‖_{L²} ≤ S / n^r`,   `n ≥ 1`,

which is (12.2.24) with the constant `c = 1`.

The orthogonal projection is at least as good as the partial sum, whose squared error is the tail
`∑_{|m| > n} c_m²` of Parseval's identity, and on that tail `|m| ≥ n` makes
`c_m² ≤ n^{-2r} |m|^{2r} c_m²`.  The Sobolev weight is the `periodicSobolevWeight` of
`Numlib/Analysis/Sobolev/Periodic`, that is the weight of Definition 7.5.1 of the book, read here
on the *real* trigonometric system rather than on the complex exponentials. -/
theorem equation_12_2_24 {r : ℝ} (hr : 0 ≤ r) {n : ℕ} (hn : 1 ≤ n) (u : L²p) {S : ℝ}
    (hS0 : 0 ≤ S)
    (hS : HasSum (fun m : ℤ => periodicSobolevWeight r m ^ 2 *
      realFourierCoeff (u : AddCircle (2 * Real.pi) → ℝ) m ^ 2) (S ^ 2)) :
    ‖u - trigProjCLM (2 * Real.pi) n u‖ ≤ S / (n : ℝ) ^ r := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnr : (0 : ℝ) < (n : ℝ) ^ r := Real.rpow_pos_of_pos (by linarith) r
  have hnr2 : (0 : ℝ) < (n : ℝ) ^ (2 * r) := Real.rpow_pos_of_pos (by linarith) _
  -- the projection is at least as good as the partial sum
  have hbest : ‖u - trigProjCLM (2 * Real.pi) n u‖ ≤ ‖u - trigPartialSum n u‖ :=
    (isBestApprox_starProjection (trigPolyLp (2 * Real.pi) n) u).2 _
      (trigPartialSum_mem_trigPolyLp n u)
  -- the squared truncation error is the Parseval tail, and the tail is bounded by the weighted sum
  have hpt : ∀ m : ℤ,
      (if m.natAbs ≤ n then 0 else realFourierCoeff (u : AddCircle (2 * Real.pi) → ℝ) m ^ 2)
        ≤ ((n : ℝ) ^ (2 * r))⁻¹ * (periodicSobolevWeight r m ^ 2 *
            realFourierCoeff (u : AddCircle (2 * Real.pi) → ℝ) m ^ 2) := by
    intro m
    by_cases hm : m.natAbs ≤ n
    · rw [ite_eq_left hm]
      have h1 : (0 : ℝ) ≤ periodicSobolevWeight r m ^ 2 *
          realFourierCoeff (u : AddCircle (2 * Real.pi) → ℝ) m ^ 2 := by positivity
      positivity
    · rw [ite_eq_right hm]
      have hm0 : m ≠ 0 := by
        rintro rfl
        exact hm (by omega)
      have hmn : (n : ℝ) ≤ |(m : ℝ)| := by
        have h1 : n ≤ m.natAbs := Nat.le_of_lt (Nat.lt_of_not_le hm)
        have h2 : (n : ℝ) ≤ ((m.natAbs : ℕ) : ℝ) := by exact_mod_cast h1
        rwa [Nat.cast_natAbs, Int.cast_abs] at h2
      have hpow : (n : ℝ) ^ (2 * r) ≤ |(m : ℝ)| ^ (2 * r) :=
        Real.rpow_le_rpow (by linarith) hmn (by linarith)
      have hc : (0 : ℝ) ≤ realFourierCoeff (u : AddCircle (2 * Real.pi) → ℝ) m ^ 2 := sq_nonneg _
      rw [periodicSobolevWeight_sq r hm0, ← mul_assoc, ← div_eq_inv_mul]
      have hratio : (1 : ℝ) ≤ |(m : ℝ)| ^ (2 * r) / (n : ℝ) ^ (2 * r) :=
        (one_le_div hnr2).2 hpow
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ |(m : ℝ)| ^ (2 * r) / (n : ℝ) ^ (2 * r) - 1 by
        linarith) hc]
  have hle : ‖u - trigPartialSum n u‖ ^ 2 ≤ ((n : ℝ) ^ (2 * r))⁻¹ * S ^ 2 :=
    hasSum_le hpt (hasSum_sq_realFourierCoeff_compl n u) (hS.mul_left _)
  have hrw : ((n : ℝ) ^ (2 * r))⁻¹ * S ^ 2 = (S / (n : ℝ) ^ r) ^ 2 := by
    rw [div_pow, ← Real.rpow_natCast ((n : ℝ) ^ r) 2, ← Real.rpow_mul (by linarith)]
    rw [show r * (2 : ℕ) = 2 * r by push_cast; ring]
    field_simp
  rw [hrw] at hle
  refine hbest.trans ?_
  have h := Real.sqrt_le_sqrt hle
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at h

/-- **(12.2.25), the Fourier–Galerkin method in `L²(0, 2π)`.**  Let `K` be a compact operator on
`L²(0, 2π)` and `λ ≠ 0` with `λ - K` invertible, and let `P_n` be the Fourier truncation.  Then
there is an `M` such that, for all large `n`, the Galerkin equations `P_n ((λ - K) u_n) = P_n f`
are uniquely solvable for every right-hand side, and whenever the exact solution lies in
`H^r(0, 2π)` with `‖u‖_{H^r} = S`,

`‖u - u_n‖_{L²} ≤ |λ| M S / n^r`.

The projections are orthogonal, so they are uniformly bounded of norm at most one
(`norm_trigProjCLM_le_one`) and converge pointwise (`tendsto_trigProjCLM`); Lemma 12.1.4 therefore
gives `‖K - P_n K‖ → 0` and Theorem 12.1.2 applies.  The rate is `equation_12_2_24` fed into
(12.1.24).

Compactness of `K` is a hypothesis rather than a consequence: on `C[a, b]` the compactness of a
continuous-kernel operator is `IntegralOperator.isCompactOperator_kernelCLM`, but on `L²` it is the
Hilbert–Schmidt theorem, which the library does not have — `IntegralOperator.l2KernelCLM` of
`Numlib/IntegralEquations/L2Kernel` bounds the operator and computes its adjoint but does not show
it compact.  The book likewise takes the compactness from its Chapter 2. -/
theorem equation_12_2_25 {K : L²p →L[ℝ] L²p} (hK : IsCompactOperator K) {μ : ℝ} (hμ : μ ≠ 0)
    {e : L²p ≃L[ℝ] L²p} (he : (e : L²p →L[ℝ] L²p) = μ • 1 - K) {r : ℝ} (hr : 0 ≤ r) :
    ∃ M : ℝ, ∀ᶠ n in atTop,
      (∀ f : L²p, ∃! un : L²p,
        IsProjectionSolution μ K (trigProjCLM (2 * Real.pi) n) f un) ∧
      ∀ (f u un : L²p) (S : ℝ), 0 ≤ S →
        HasSum (fun m : ℤ => periodicSobolevWeight r m ^ 2 *
          realFourierCoeff (u : AddCircle (2 * Real.pi) → ℝ) m ^ 2) (S ^ 2) →
        (μ • 1 - K : L²p →L[ℝ] L²p) u = f →
        IsProjectionSolution μ K (trigProjCLM (2 * Real.pi) n) f un →
        ‖u - un‖ ≤ ‖μ‖ * M * (S / (n : ℝ) ^ r) := by
  set A : ℝ := ‖(e.symm : L²p →L[ℝ] L²p)‖ with hAdef
  have hA0 : (0 : ℝ) ≤ A := norm_nonneg _
  have hconv : Tendsto (fun n => ‖K - trigProjCLM (2 * Real.pi) n ∘L K‖) atTop (𝓝 0) :=
    lemma_12_1_4 hK fun x => tendsto_trigProjCLM x
  refine ⟨2 * A, ?_⟩
  have hsmall : ∀ᶠ n in atTop,
      A * ‖K - trigProjCLM (2 * Real.pi) n ∘L K‖ < 1 / 2 := by
    have h0 : Tendsto (fun n => A * ‖K - trigProjCLM (2 * Real.pi) n ∘L K‖) atTop (𝓝 0) := by
      simpa using hconv.const_mul A
    exact h0.eventually (eventually_lt_nhds (by norm_num))
  filter_upwards [hsmall, eventually_ge_atTop 1] with n hn hn1
  obtain ⟨e', he'coe, he'norm, huniq⟩ :=
    theorem_12_1_2 hμ (isIdempotentElem_trigProjCLM (2 * Real.pi) n) e he (by linarith)
  have hb1 : ‖(e'.symm : L²p →L[ℝ] L²p)‖ ≤ 2 * A := by
    refine he'norm.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith [norm_nonneg (K - trigProjCLM (2 * Real.pi) n ∘L K)]
  refine ⟨huniq, fun f u un S hS0 hS hu hun => ?_⟩
  have hrate : ‖u - trigProjCLM (2 * Real.pi) n u‖ ≤ S / (n : ℝ) ^ r :=
    equation_12_2_24 hr hn1 u hS0 hS
  have hkey := (equation_12_1_24 (isIdempotentElem_trigProjCLM (2 * Real.pi) n) he'coe hu hun).2
  calc ‖u - un‖
      ≤ ‖μ‖ * ‖(e'.symm : L²p →L[ℝ] L²p)‖ * ‖u - trigProjCLM (2 * Real.pi) n u‖ := hkey
    _ ≤ ‖μ‖ * (2 * A) * (S / (n : ℝ) ^ r) := by gcongr

end Fourier

/-! ### The piecewise linear Galerkin method in `L²` -/

section Galerkin

open MeasureTheory IntegralOperator

variable {a b : ℝ}

/-- **(12.2.19), the piecewise linear Galerkin method of §12.2.3.**  Let `K` be a compact operator
on `L²(a, b)`, let `λ ≠ 0` be such that `λ - K` is invertible, and let `P_n` be the `L²`-orthogonal
projection onto the continuous piecewise linear functions of a sequence of partitions of `[a, b]`
whose mesh `h_n` tends to zero.  Then:

* `‖K - P_n K‖ → 0`, which is (12.1.21);
* for all large `n` the Galerkin equations `P_n ((λ - K) u_n) = P_n f` have a unique solution for
  every right-hand side;
* and if the exact solution is (the class of) a `C²` function with `|u''| ≤ M₂` on `[a, b]`, then

  `‖u - u_n‖_{L²} ≤ |λ| M √(b - a) h_n² M₂ / 8`

  with `M = 2 ‖(λ - K)⁻¹‖` independent of `n`.

The projections have norm one for free, being orthogonal, and converge pointwise by
`tendsto_piecewiseLinearProjCLM`, so Lemma 12.1.4 applies; the approximation-theoretic input is
(12.2.18) followed by `norm_sub_piecewiseLinearInterpCLM_le`, exactly as the book does it — no `L²`
interpolation estimate is needed.

Compactness of `K` on `L²` is a hypothesis, as it is in `equation_12_2_25`: on `C[a, b]` the
compactness of a continuous-kernel operator is `IntegralOperator.isCompactOperator_fredholm`, but on
`L²` it is the Hilbert–Schmidt theorem, which the library does not have. -/
theorem equation_12_2_19 (hab : a ≤ b) {μ : ℝ} (hμ : μ ≠ 0)
    {K : Lp ℝ 2 (IntegralOperator.iccMeasure a b) →L[ℝ]
      Lp ℝ 2 (IntegralOperator.iccMeasure a b)} (hK : IsCompactOperator K)
    {N : ℕ → ℕ} {y : ℕ → ℕ → Set.Icc a b} {h : ℕ → ℝ}
    (hstep : ∀ n, ∀ i ≤ N n, (y n i : ℝ) < (y n (i + 1) : ℝ))
    (hfirst : ∀ n, (y n 0 : ℝ) = a) (hlast : ∀ n, (y n (N n + 1) : ℝ) = b)
    (hmesh : ∀ n, ∀ i ≤ N n, (y n (i + 1) : ℝ) - (y n i : ℝ) ≤ h n)
    (hh : Tendsto h atTop (𝓝 0))
    {e : Lp ℝ 2 (IntegralOperator.iccMeasure a b) ≃L[ℝ]
      Lp ℝ 2 (IntegralOperator.iccMeasure a b)}
    (he : (e : Lp ℝ 2 (IntegralOperator.iccMeasure a b) →L[ℝ]
      Lp ℝ 2 (IntegralOperator.iccMeasure a b)) = μ • 1 - K) :
    Tendsto (fun n => ‖K - piecewiseLinearProjCLM a b (N n) (y n) ∘L K‖) atTop (𝓝 0) ∧
      ∃ M : ℝ, ∀ᶠ n in atTop,
        (∀ f : Lp ℝ 2 (IntegralOperator.iccMeasure a b),
          ∃! un : Lp ℝ 2 (IntegralOperator.iccMeasure a b),
            IsProjectionSolution μ K (piecewiseLinearProjCLM a b (N n) (y n)) f un) ∧
        ∀ (g : ℝ → ℝ) (M₂ : ℝ) (uc : C(Set.Icc a b, ℝ))
          (f un : Lp ℝ 2 (IntegralOperator.iccMeasure a b)),
          ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) g → (∀ t : Set.Icc a b, uc t = g (t : ℝ)) →
          (∀ t ∈ Set.Icc a b, |iteratedDeriv 2 g t| ≤ M₂) →
          (μ • 1 - K : Lp ℝ 2 (IntegralOperator.iccMeasure a b) →L[ℝ]
            Lp ℝ 2 (IntegralOperator.iccMeasure a b)) (iccToLp a b uc) = f →
          IsProjectionSolution μ K (piecewiseLinearProjCLM a b (N n) (y n)) f un →
          ‖iccToLp a b uc - un‖ ≤ ‖μ‖ * M * (√(b - a) * (h n ^ 2 / 8 * M₂)) := by
  set A : ℝ := ‖(e.symm : Lp ℝ 2 (IntegralOperator.iccMeasure a b) →L[ℝ]
    Lp ℝ 2 (IntegralOperator.iccMeasure a b))‖ with hAdef
  have hA0 : (0 : ℝ) ≤ A := norm_nonneg _
  have hconv : Tendsto (fun n => ‖K - piecewiseLinearProjCLM a b (N n) (y n) ∘L K‖) atTop (𝓝 0) :=
    lemma_12_1_4 hK (tendsto_piecewiseLinearProjCLM hab hstep hfirst hlast hmesh hh)
  refine ⟨hconv, ⟨2 * A, ?_⟩⟩
  have hsmall : ∀ᶠ n in atTop,
      A * ‖K - piecewiseLinearProjCLM a b (N n) (y n) ∘L K‖ < 1 / 2 := by
    have h0 : Tendsto (fun n => A * ‖K - piecewiseLinearProjCLM a b (N n) (y n) ∘L K‖)
        atTop (𝓝 0) := by simpa using hconv.const_mul A
    exact h0.eventually (eventually_lt_nhds (by norm_num))
  filter_upwards [hsmall] with n hn
  obtain ⟨e', he'coe, he'norm, huniq⟩ :=
    theorem_12_1_2 hμ (isIdempotentElem_piecewiseLinearProjCLM a b (N n) (y n)) e he
      (by linarith)
  have hb1 : ‖(e'.symm : Lp ℝ 2 (IntegralOperator.iccMeasure a b) →L[ℝ]
      Lp ℝ 2 (IntegralOperator.iccMeasure a b))‖ ≤ 2 * A := by
    refine he'norm.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith [norm_nonneg (K - piecewiseLinearProjCLM a b (N n) (y n) ∘L K)]
  refine ⟨huniq, fun g M₂ uc f un hg huc hM₂ hu hun => ?_⟩
  have hb2 : ‖iccToLp a b uc - piecewiseLinearProjCLM a b (N n) (y n) (iccToLp a b uc)‖
      ≤ √(b - a) * (h n ^ 2 / 8 * M₂) := by
    refine (norm_sub_piecewiseLinearProjCLM_le hab (N n) (y n) uc).trans ?_
    exact mul_le_mul_of_nonneg_left
      (norm_sub_piecewiseLinearInterpCLM_le (hstep n) (hfirst n) (hlast n) hg huc (hmesh n) hM₂)
      (Real.sqrt_nonneg _)
  have hkey := (equation_12_1_24 (isIdempotentElem_piecewiseLinearProjCLM a b (N n) (y n))
    he'coe hu hun).2
  calc ‖iccToLp a b uc - un‖
      ≤ ‖μ‖ * ‖(e'.symm : Lp ℝ 2 (IntegralOperator.iccMeasure a b) →L[ℝ]
            Lp ℝ 2 (IntegralOperator.iccMeasure a b))‖ *
          ‖iccToLp a b uc - piecewiseLinearProjCLM a b (N n) (y n) (iccToLp a b uc)‖ := hkey
    _ ≤ ‖μ‖ * (2 * A) * (√(b - a) * (h n ^ 2 / 8 * M₂)) := by gcongr

end Galerkin

end AtkinsonHan.Chapter12
