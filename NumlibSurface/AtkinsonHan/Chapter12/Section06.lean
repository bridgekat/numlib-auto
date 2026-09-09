import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import NumlibSurface.AtkinsonHan.Chapter12.Section04

/-!
# Atkinson–Han §12.6: iteration methods for the discretized equations

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §12.6.

The linear systems produced by the methods of this chapter are large and dense, so they are solved
by residual correction rather than by elimination.  §12.6.2 is the two-grid iteration for the
Nyström method: the residual of the *fine* equation `(λ - K_n) u_n = f` is corrected with the
inverse of the *coarse* operator `λ - K_m`, which is the only inverse ever formed.  As in §12.1 the
book's scalar `λ` is written `μ`, `λ` being Lean's lambda binder.

## Main results

* `twoGridStep`, `equation_12_6_20` — (12.6.20)–(12.6.22), the residual, the coarse correction and
  the update, as one step of the residual correction method (12.6.5)–(12.6.6) whose approximate
  inverse `C_n` is `(λ - K_m)⁻¹`.
* `twoGridOperator`, `equation_12_6_27` — (12.6.27)–(12.6.28), the error identity
  `u_n - u_n^{(κ+1)} = M_{m,n} (u_n - u_n^{(κ)})` with
  `M_{m,n} = (1/λ) (λ - K_m)⁻¹ (K_n - K_m) K_n`, and the geometric bound it gives.
* `theorem_12_6_1` — for a collectively compact, pointwise convergent family with `λ - K`
  invertible, every large enough coarse index `m` makes `λ - K_m` invertible and `‖M_{m,n}‖ < 1`
  for *every* fine index `n ≥ m`, so the two-grid iterates converge to `u_n` from every starting
  point.
* `periodicPoissonKernel` and `example_12_6_2` — the kernel `k_γ` of (12.6.43) and its spectrum
  (12.6.44), `γ^j` on `cos (2 j π x)` and `-γ^j` on `sin (2 j π x)`, which is why the book computes
  with this equation.

## Not formalized here

§12.6.3, the translation of the operator iteration into the linear system `A_n u_n = f_n`, and
§12.6.4, the operation count.  Both are implementation, with no theorem content.

Table 12.4 of Example 12.6.2 — the iteration counts, the errors and the empirical convergence
ratios `ν̃` of the two-grid iteration at `γ = 0.8` — is computed floating-point data and is not
stated.  Only (12.6.44), the spectrum of the kernel, is; the convergence the table exhibits is
`theorem_12_6_1`, and the mesh independence principle discussed after it is the limit (12.6.48),
which the book states without proof.

## Conventions

As in §12.4, the book's family `K_n` is `K n` here and its pointwise limit `K` is `L`.

The book states Theorem 12.6.1 for the Nyström operators of §12.4 on `C(D)`.  Its proof uses only
that the family is collectively compact and pointwise convergent — the assumptions A1–A3 of
`IsCollectivelyCompactFamily` — so that is the form stated here, and the Nyström case is the
instance.  The two indices both have to be large for a reason that the book's `n, m → ∞` hides:
`(K_n - K_m) K_n` splits into `(K_n - K) K_n`, which needs `n` large, and `(K - K_m) K_n`, which
has to be small *uniformly in `n`* and so is not covered by the diagonal estimate
`lemma_12_4_7_d`.
-/

open Filter Topology

open scoped Real

namespace AtkinsonHan.Chapter12

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-! ### The two-grid iteration -/

/-- **(12.6.20)–(12.6.22)**, one step of the two-grid iteration for the fine equation
`(λ - K_n) u = f`: form the residual `r = f - (λ - K_n) u`, correct it with the *coarse* inverse,
`δ = (λ - K_m)⁻¹ (K_n r)`, and update `u ↦ u + (r + δ)/λ`.

The coarse equivalence is carried as `e : X ≃L[𝕜] X` with `↑e = λ - K_m`, so that `e.symm` is a
genuine inverse; it is the approximate inverse `C_n` of the residual correction method
(12.6.5)–(12.6.6), and the only inverse the method ever forms.  This is the backbone
`SecondKind.twoGridStep`. -/
noncomputable abbrev twoGridStep (μ : 𝕜) (e : X ≃L[𝕜] X) (Kn : X →L[𝕜] X) (f u : X) : X :=
  SecondKind.twoGridStep μ e Kn f u

/-- The three displays **(12.6.20)–(12.6.22)** written out: the residual `r_n^{(κ)}`, and the
update built from it and from the coarse correction. -/
theorem equation_12_6_20 (μ : 𝕜) (e : X ≃L[𝕜] X) (Kn : X →L[𝕜] X) (f u : X) :
    SecondKind.residual μ Kn f u = f - (μ • 1 - Kn : X →L[𝕜] X) u ∧
      twoGridStep μ e Kn f u = u + μ⁻¹ • (SecondKind.residual μ Kn f u
        + e.symm (Kn (SecondKind.residual μ Kn f u))) :=
  ⟨rfl, rfl⟩

/-- **(12.6.28)**, the iteration operator `M_{m,n} = (1/λ) (λ - K_m)⁻¹ (K_n - K_m) K_n` of the
two-grid method, where `e` is the coarse equivalence `↑e = λ - K_m`.  The factor `K_n - K_m`
appears composed with `K_n`, which is the shape that collective compactness makes small even
though `‖K_n - K_m‖` does not tend to zero.  This is the backbone
`SecondKind.twoGridOperator`. -/
noncomputable abbrev twoGridOperator (μ : 𝕜) (e : X ≃L[𝕜] X) (Km Kn : X →L[𝕜] X) : X →L[𝕜] X :=
  SecondKind.twoGridOperator μ e Km Kn

/-- **(12.6.27)** and its consequence: if `u_n` solves the fine equation `(λ - K_n) u_n = f`, then
one two-grid step multiplies the error by `M_{m,n}`,

`u_n - u_n^{(κ+1)} = M_{m,n} (u_n - u_n^{(κ)})`,

and hence `‖u_n - u_n^{(κ)}‖ ≤ ‖M_{m,n}‖^κ ‖u_n - u_n^{(0)}‖`.  The identity is algebra: no
compactness, no completeness and no bound on `M_{m,n}` is used. -/
theorem equation_12_6_27 {μ : 𝕜} (hμ : μ ≠ 0) {e : X ≃L[𝕜] X} {Km Kn : X →L[𝕜] X}
    (he : (e : X →L[𝕜] X) = μ • 1 - Km) {f ustar : X}
    (hstar : (μ • 1 - Kn : X →L[𝕜] X) ustar = f) (u : X) :
    ustar - twoGridStep μ e Kn f u = twoGridOperator μ e Km Kn (ustar - u) ∧
      ∀ k : ℕ, ‖ustar - (twoGridStep μ e Kn f)^[k] u‖ ≤
        ‖twoGridOperator μ e Km Kn‖ ^ k * ‖ustar - u‖ :=
  ⟨SecondKind.twoGrid_error_eq hμ he hstar u,
    SecondKind.norm_sub_twoGridStep_iterate_le hμ he hstar u⟩

/-! ### Convergence -/

variable {K : ℕ → X →L[𝕜] X} {L : X →L[𝕜] X}

/-- **Theorem 12.6.1**: let `{K_p}` be a collectively compact family converging pointwise to `K`,
with `λ ≠ 0` and `λ - K` invertible.  Then for every sufficiently large coarse index `m` the
coarse operator `λ - K_m` is invertible and, for *every* fine index `n ≥ m`,

`‖M_{m,n}‖ < 1`,

so the two-grid iterates converge to the solution `u_n` of `(λ - K_n) u_n = f` from every starting
point, geometrically by `equation_12_6_27`.

The book states this for the Nyström operators on `C(D)`; the proof uses only the assumptions
A1–A3, which is `IsCollectivelyCompactFamily`.  Both indices have to be large: `(K_n - K_m) K_n`
splits into `(K_n - K) K_n`, which `lemma_12_4_7_d` makes small for large `n`, and `(K - K_m) K_n`,
which must be small uniformly in `n` and is the backbone
`SecondKind.eventually_forall_opNorm_sub_comp_lt`. -/
theorem theorem_12_6_1 [CompleteSpace X] {μ : 𝕜} (hμ : μ ≠ 0)
    (h : IsCollectivelyCompactFamily K L) {e : X ≃L[𝕜] X} (he : (e : X →L[𝕜] X) = μ • 1 - L) :
    ∀ᶠ m in atTop, ∃ em : X ≃L[𝕜] X, (em : X →L[𝕜] X) = μ • 1 - K m ∧
      ∀ n ≥ m, ‖twoGridOperator μ em (K m) (K n)‖ < 1 ∧
        ∀ f un : X, (μ • 1 - K n : X →L[𝕜] X) un = f → ∀ u₀ : X,
          Tendsto (fun k => (twoGridStep μ em (K n) f)^[k] u₀) atTop (𝓝 un) := by
  filter_upwards [SecondKind.eventually_norm_twoGridOperator_lt_one hμ h.isCollectivelyCompact
    h.tendsto he] with m hm
  obtain ⟨em, hem, hlt⟩ := hm
  exact ⟨em, hem, fun n hn =>
    ⟨hlt n hn, fun f un hun u₀ => SecondKind.tendsto_twoGridIterate hμ hem (hlt n hn) hun u₀⟩⟩

section Poisson

open Complex InnerProductSpace Metric

variable {γ : ℝ}

private theorem poissonKernel_circleMap (γ θ : ℝ) (hγ0 : 0 ≤ γ) :
    poissonKernel 0 (γ : ℂ) (circleMap 0 1 θ)
      = (1 - γ ^ 2) / (1 + γ ^ 2 - 2 * γ * Real.cos θ) := by
  have hz : circleMap 0 1 θ = Complex.exp (θ * Complex.I) := by simp [circleMap]
  rw [poissonKernel_def, hz]
  have h1 : ‖Complex.exp (θ * Complex.I) - 0‖ = 1 := by simp [Complex.norm_exp_ofReal_mul_I]
  have h2 : ‖(γ : ℂ) - 0‖ = γ := by simp [abs_of_nonneg hγ0]
  have h3 : ‖Complex.exp (θ * Complex.I) - 0 - ((γ : ℂ) - 0)‖ ^ 2
      = 1 + γ ^ 2 - 2 * γ * Real.cos θ := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [h1, h2, h3]
  norm_num

private theorem circleMap_pow_re (j : ℕ) (θ : ℝ) :
    ((circleMap 0 1 θ) ^ j).re = Real.cos (j * θ) := by
  have hz : circleMap 0 1 θ = Complex.exp (θ * Complex.I) := by simp [circleMap]
  rw [hz, ← Complex.exp_nat_mul,
    show (j : ℂ) * ((θ : ℂ) * Complex.I) = ((j * θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I_re]

private theorem circleMap_pow_im (j : ℕ) (θ : ℝ) :
    ((circleMap 0 1 θ) ^ j).im = Real.sin (j * θ) := by
  have hz : circleMap 0 1 θ = Complex.exp (θ * Complex.I) := by simp [circleMap]
  rw [hz, ← Complex.exp_nat_mul,
    show (j : ℂ) * ((θ : ℂ) * Complex.I) = ((j * θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I_im]

private theorem integral_poisson_cos (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (j : ℕ) :
    (∫ θ in (0 : ℝ)..(2 * π),
        (1 - γ ^ 2) / (1 + γ ^ 2 - 2 * γ * Real.cos θ) * Real.cos (j * θ))
      = 2 * π * γ ^ j := by
  have hw : (γ : ℂ) ∈ ball (0 : ℂ) 1 := by
    simp [Complex.norm_real, abs_of_nonneg hγ0, hγ1]
  have hana : ∀ x : ℂ, AnalyticAt ℂ (fun z : ℂ => z ^ j) x := fun _ =>
    AnalyticAt.pow analyticAt_id j
  have hf : HarmonicOnNhd (fun z : ℂ => (z ^ j).re) (closedBall (0 : ℂ) 1) := fun x _ =>
    AnalyticAt.harmonicAt_re (hana x)
  have key := hf.circleAverage_poissonKernel_smul hw
  rw [Real.circleAverage_def] at key
  have hint : (∫ θ in (0 : ℝ)..(2 * π),
      (poissonKernel 0 (γ : ℂ) • fun z : ℂ => (z ^ j).re) (circleMap 0 1 θ))
      = ∫ θ in (0 : ℝ)..(2 * π),
        (1 - γ ^ 2) / (1 + γ ^ 2 - 2 * γ * Real.cos θ) * Real.cos (j * θ) := by
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [Pi.smul_apply', smul_eq_mul]
    rw [poissonKernel_circleMap γ θ hγ0, circleMap_pow_re]
  rw [hint] at key
  rw [show ((γ : ℂ) ^ j).re = γ ^ j by rw [← Complex.ofReal_pow, Complex.ofReal_re],
    smul_eq_mul] at key
  have h2π : (2 * π : ℝ) ≠ 0 := by positivity
  have h : (2 * π) * ((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π),
      (1 - γ ^ 2) / (1 + γ ^ 2 - 2 * γ * Real.cos θ) * Real.cos (j * θ))
      = (2 * π) * γ ^ j := by rw [key]
  rwa [← mul_assoc, mul_inv_cancel₀ h2π, one_mul] at h

private theorem integral_poisson_sin (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (j : ℕ) :
    (∫ θ in (0 : ℝ)..(2 * π),
        (1 - γ ^ 2) / (1 + γ ^ 2 - 2 * γ * Real.cos θ) * Real.sin (j * θ)) = 0 := by
  have hw : (γ : ℂ) ∈ ball (0 : ℂ) 1 := by
    simp [Complex.norm_real, abs_of_nonneg hγ0, hγ1]
  have hana : ∀ x : ℂ, AnalyticAt ℂ (fun z : ℂ => z ^ j) x := fun _ =>
    AnalyticAt.pow analyticAt_id j
  have hf : HarmonicOnNhd (fun z : ℂ => (z ^ j).im) (closedBall (0 : ℂ) 1) := fun x _ =>
    AnalyticAt.harmonicAt_im (hana x)
  have key := hf.circleAverage_poissonKernel_smul hw
  rw [Real.circleAverage_def] at key
  have hint : (∫ θ in (0 : ℝ)..(2 * π),
      (poissonKernel 0 (γ : ℂ) • fun z : ℂ => (z ^ j).im) (circleMap 0 1 θ))
      = ∫ θ in (0 : ℝ)..(2 * π),
        (1 - γ ^ 2) / (1 + γ ^ 2 - 2 * γ * Real.cos θ) * Real.sin (j * θ) := by
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [Pi.smul_apply', smul_eq_mul]
    rw [poissonKernel_circleMap γ θ hγ0, circleMap_pow_im]
  rw [hint] at key
  rw [show ((γ : ℂ) ^ j).im = 0 by rw [← Complex.ofReal_pow, Complex.ofReal_im],
    smul_eq_mul] at key
  have h2π : (2 * π : ℝ) ≠ 0 := by positivity
  have h : (2 * π) * ((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π),
      (1 - γ ^ 2) / (1 + γ ^ 2 - 2 * γ * Real.cos θ) * Real.sin (j * θ))
      = (2 * π) * 0 := by rw [key]
  rwa [← mul_assoc, mul_inv_cancel₀ h2π, one_mul, mul_zero] at h

/-- **The kernel `k_γ` of (12.6.43)**, the Poisson kernel of the unit disk read as a `1`-periodic
function of the parameter,

`k_γ(τ) = (1 - γ²) / (1 + γ² - 2 γ cos (2 π τ))`,

for `0 ≤ γ < 1`.  The book writes it also as its Fourier series `1 + 2 ∑_j γ^j cos (2 j π τ)`; that
expansion is not needed here, because the eigenvalue relations (12.6.44) come from the Poisson
integral formula directly.

The equation (12.6.43) with this kernel is the reformulation of the Dirichlet problem for Laplace's
equation on an elliptical region, which is why its spectrum is known in closed form. -/
noncomputable def periodicPoissonKernel (γ τ : ℝ) : ℝ :=
  (1 - γ ^ 2) / (1 + γ ^ 2 - 2 * γ * Real.cos (2 * π * τ))

/-- The denominator of `k_γ` never vanishes for `0 ≤ γ < 1`: it is
`(1 - γ)² + 2 γ (1 - cos (2 π τ)) ≥ (1 - γ)² > 0`. -/
theorem periodicPoissonKernel_denom_pos (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (τ : ℝ) :
    0 < 1 + γ ^ 2 - 2 * γ * Real.cos (2 * π * τ) := by
  nlinarith [mul_nonneg hγ0 (sub_nonneg.2 (Real.cos_le_one (2 * π * τ))),
    mul_pos (sub_pos.2 hγ1) (sub_pos.2 hγ1)]

/-- `k_γ` is continuous, its denominator being bounded away from zero. -/
theorem continuous_periodicPoissonKernel (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    Continuous (periodicPoissonKernel γ) :=
  continuous_const.div (by fun_prop) fun τ => (periodicPoissonKernel_denom_pos hγ0 hγ1 τ).ne'

/-- `k_γ` has period `1`, which is what lets the operator of (12.6.43) be read on the Fourier modes
of the interval. -/
theorem periodic_periodicPoissonKernel (γ : ℝ) :
    Function.Periodic (periodicPoissonKernel γ) 1 := by
  intro τ
  rw [periodicPoissonKernel, periodicPoissonKernel,
    show 2 * π * (τ + 1) = 2 * π * τ + 2 * π by ring, Real.cos_add_two_pi]

/-- The `j`-th cosine coefficient of `k_γ` is `γ^j`.  This is the Poisson integral formula,
Mathlib's `HarmonicOnNhd.circleAverage_poissonKernel_smul`, at the harmonic function `z ↦ Re (zʲ)`
and the interior point `γ`, rescaled from `[0, 2π]` to `[0, 1]`. -/
theorem integral_periodicPoissonKernel_mul_cos (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (j : ℕ) :
    (∫ τ in (0 : ℝ)..1, periodicPoissonKernel γ τ * Real.cos (2 * j * π * τ)) = γ ^ j := by
  have h2π : (2 * π : ℝ) ≠ 0 := by positivity
  have hcomp : (∫ τ in (0 : ℝ)..1, (1 - γ ^ 2) / (1 + γ ^ 2 - 2 * γ * Real.cos (2 * π * τ))
        * Real.cos ((j : ℝ) * (2 * π * τ)))
      = (2 * π)⁻¹ • ∫ θ in (2 * π * 0)..(2 * π * 1),
          (1 - γ ^ 2) / (1 + γ ^ 2 - 2 * γ * Real.cos θ) * Real.cos ((j : ℝ) * θ) :=
    intervalIntegral.integral_comp_mul_left
      (fun θ : ℝ => (1 - γ ^ 2) / (1 + γ ^ 2 - 2 * γ * Real.cos θ) * Real.cos ((j : ℝ) * θ)) h2π
  rw [mul_zero, mul_one, integral_poisson_cos hγ0 hγ1 j, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ h2π, one_mul] at hcomp
  calc (∫ τ in (0 : ℝ)..1, periodicPoissonKernel γ τ * Real.cos (2 * j * π * τ))
      = ∫ τ in (0 : ℝ)..1, (1 - γ ^ 2) / (1 + γ ^ 2 - 2 * γ * Real.cos (2 * π * τ))
          * Real.cos ((j : ℝ) * (2 * π * τ)) :=
        intervalIntegral.integral_congr fun τ _ => by
          rw [periodicPoissonKernel, show (j : ℝ) * (2 * π * τ) = 2 * j * π * τ by ring]
    _ = γ ^ j := hcomp

/-- The `j`-th sine coefficient of `k_γ` vanishes: the same Poisson integral formula at
`z ↦ Im (zʲ)`, whose value at the *real* point `γ` is zero. -/
theorem integral_periodicPoissonKernel_mul_sin (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (j : ℕ) :
    (∫ τ in (0 : ℝ)..1, periodicPoissonKernel γ τ * Real.sin (2 * j * π * τ)) = 0 := by
  have h2π : (2 * π : ℝ) ≠ 0 := by positivity
  have hcomp : (∫ τ in (0 : ℝ)..1, (1 - γ ^ 2) / (1 + γ ^ 2 - 2 * γ * Real.cos (2 * π * τ))
        * Real.sin ((j : ℝ) * (2 * π * τ)))
      = (2 * π)⁻¹ • ∫ θ in (2 * π * 0)..(2 * π * 1),
          (1 - γ ^ 2) / (1 + γ ^ 2 - 2 * γ * Real.cos θ) * Real.sin ((j : ℝ) * θ) :=
    intervalIntegral.integral_comp_mul_left
      (fun θ : ℝ => (1 - γ ^ 2) / (1 + γ ^ 2 - 2 * γ * Real.cos θ) * Real.sin ((j : ℝ) * θ)) h2π
  rw [mul_zero, mul_one, integral_poisson_sin hγ0 hγ1 j, smul_eq_mul, mul_zero] at hcomp
  calc (∫ τ in (0 : ℝ)..1, periodicPoissonKernel γ τ * Real.sin (2 * j * π * τ))
      = ∫ τ in (0 : ℝ)..1, (1 - γ ^ 2) / (1 + γ ^ 2 - 2 * γ * Real.cos (2 * π * τ))
          * Real.sin ((j : ℝ) * (2 * π * τ)) :=
        intervalIntegral.integral_congr fun τ _ => by
          rw [periodicPoissonKernel, show (j : ℝ) * (2 * π * τ) = 2 * j * π * τ by ring]
    _ = 0 := hcomp

/-- **(12.6.44), the spectrum of the kernel of Example 12.6.2.**  For the integral operator

`K u (x) = ∫₀¹ k_γ(x + y) u(y) dy`,  `0 ≤ γ < 1`,

of (12.6.43), the eigenvalues and eigenfunctions are

`γ^j` with `cos (2 j π x)`, `j = 0, 1, 2, …`,  and  `-γ^j` with `sin (2 j π x)`, `j = 1, 2, …`,

which is what makes this equation a test problem: the exact solution of `(λ - K) u = f` is known
for every trigonometric `f`, and `λ` can be placed anywhere relative to the spectrum.  The `j = 0`
case of the second display is the trivial `0 = 0`, so both are stated for every `j`.

The proof is the Poisson integral formula: `k_γ` is the Poisson kernel of the unit disk at the
interior point `γ`, so integrating it against the boundary values of a harmonic function returns
the value at `γ`, and `cos (2 j π ·)` and `sin (2 j π ·)` are the boundary values of `Re (zʲ)` and
`Im (zʲ)`.  The shift `x + y` is absorbed by the periodicity of `k_γ`, and the addition formulas
then split the integral into the two coefficients.

Table 12.4 of the example — the measured iteration counts and error reductions of the two-grid
iteration at `γ = 0.8` — is not stated: those are computed floating-point numbers.  The convergence
they illustrate is `theorem_12_6_1`. -/
theorem example_12_6_2 (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (j : ℕ) (x : ℝ) :
    (∫ y in (0 : ℝ)..1, periodicPoissonKernel γ (x + y) * Real.cos (2 * j * π * y))
        = γ ^ j * Real.cos (2 * j * π * x) ∧
      (∫ y in (0 : ℝ)..1, periodicPoissonKernel γ (x + y) * Real.sin (2 * j * π * y))
        = -(γ ^ j) * Real.sin (2 * j * π * x) := by
  have hcont := continuous_periodicPoissonKernel hγ0 hγ1
  have hper := periodic_periodicPoissonKernel γ
  have hcos : Continuous fun τ : ℝ => periodicPoissonKernel γ τ * Real.cos (2 * j * π * τ) :=
    hcont.mul (by fun_prop)
  have hsin : Continuous fun τ : ℝ => periodicPoissonKernel γ τ * Real.sin (2 * j * π * τ) :=
    hcont.mul (by fun_prop)
  have shift : ∀ g : ℝ → ℝ, Function.Periodic g 1 →
      (∫ y in (0 : ℝ)..1, g (x + y)) = ∫ τ in (0 : ℝ)..1, g τ := by
    intro g hg
    rw [intervalIntegral.integral_comp_add_left g x, add_zero]
    have h := hg.intervalIntegral_add_eq x 0
    rwa [zero_add] at h
  constructor
  · have hg : Function.Periodic
        (fun τ : ℝ => periodicPoissonKernel γ τ * Real.cos (2 * j * π * (τ - x))) 1 := fun τ => by
      simp only [hper τ,
        show 2 * (j : ℝ) * π * (τ + 1 - x) = 2 * j * π * (τ - x) + j * (2 * π) by ring,
        Real.cos_add_nat_mul_two_pi]
    calc (∫ y in (0 : ℝ)..1, periodicPoissonKernel γ (x + y) * Real.cos (2 * j * π * y))
        = ∫ y in (0 : ℝ)..1,
            periodicPoissonKernel γ (x + y) * Real.cos (2 * j * π * (x + y - x)) :=
          intervalIntegral.integral_congr fun y _ => by rw [show x + y - x = y by ring]
      _ = ∫ τ in (0 : ℝ)..1, periodicPoissonKernel γ τ * Real.cos (2 * j * π * (τ - x)) :=
          shift _ hg
      _ = ∫ τ in (0 : ℝ)..1,
            (Real.cos (2 * j * π * x) *
                (periodicPoissonKernel γ τ * Real.cos (2 * j * π * τ))
              + Real.sin (2 * j * π * x) *
                (periodicPoissonKernel γ τ * Real.sin (2 * j * π * τ))) :=
          intervalIntegral.integral_congr fun τ _ => by
            rw [show 2 * (j : ℝ) * π * (τ - x) = 2 * j * π * τ - 2 * j * π * x by ring,
              Real.cos_sub]
            ring
      _ = γ ^ j * Real.cos (2 * j * π * x) := by
          rw [intervalIntegral.integral_add ((hcos.const_mul _).intervalIntegrable 0 1)
              ((hsin.const_mul _).intervalIntegrable 0 1),
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
            integral_periodicPoissonKernel_mul_cos hγ0 hγ1 j,
            integral_periodicPoissonKernel_mul_sin hγ0 hγ1 j]
          ring
  · have hg : Function.Periodic
        (fun τ : ℝ => periodicPoissonKernel γ τ * Real.sin (2 * j * π * (τ - x))) 1 := fun τ => by
      simp only [hper τ,
        show 2 * (j : ℝ) * π * (τ + 1 - x) = 2 * j * π * (τ - x) + j * (2 * π) by ring,
        Real.sin_add_nat_mul_two_pi]
    calc (∫ y in (0 : ℝ)..1, periodicPoissonKernel γ (x + y) * Real.sin (2 * j * π * y))
        = ∫ y in (0 : ℝ)..1,
            periodicPoissonKernel γ (x + y) * Real.sin (2 * j * π * (x + y - x)) :=
          intervalIntegral.integral_congr fun y _ => by rw [show x + y - x = y by ring]
      _ = ∫ τ in (0 : ℝ)..1, periodicPoissonKernel γ τ * Real.sin (2 * j * π * (τ - x)) :=
          shift _ hg
      _ = ∫ τ in (0 : ℝ)..1,
            (Real.cos (2 * j * π * x) *
                (periodicPoissonKernel γ τ * Real.sin (2 * j * π * τ))
              + -Real.sin (2 * j * π * x) *
                (periodicPoissonKernel γ τ * Real.cos (2 * j * π * τ))) :=
          intervalIntegral.integral_congr fun τ _ => by
            rw [show 2 * (j : ℝ) * π * (τ - x) = 2 * j * π * τ - 2 * j * π * x by ring,
              Real.sin_sub]
            ring
      _ = -(γ ^ j) * Real.sin (2 * j * π * x) := by
          rw [intervalIntegral.integral_add ((hsin.const_mul _).intervalIntegrable 0 1)
              ((hcos.const_mul _).intervalIntegrable 0 1),
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
            integral_periodicPoissonKernel_mul_cos hγ0 hγ1 j,
            integral_periodicPoissonKernel_mul_sin hγ0 hγ1 j]
          ring

end Poisson

end AtkinsonHan.Chapter12
