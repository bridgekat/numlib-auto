import Numlib.Approximation.GradedMesh
import Numlib.IntegralEquations.ProductIntegration
import NumlibSurface.AtkinsonHan.Chapter12.Section01
import NumlibSurface.AtkinsonHan.Chapter12.Section04

/-!
# Atkinson–Han §12.5: product integration

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §12.5.

The equation is `λ u - K u = f` with the *weakly singular* kernel `k (x, y) = l (x, y) g (x, y)`,
`l` continuous and `g` singular but satisfying the two conditions (12.5.15)–(12.5.16) — the
conditions (A₂) and (A₁) of `IntegralOperator.IsAdmissibleKernel`.  The product integration method
replaces the smooth factor `y ↦ l (x, y) u (y)` of the integrand by its piecewise polynomial
interpolant and integrates the singular factor exactly:

`K_n u (x) = ∫ [l (x, ·) u (·)]_n (y) g (x, y) dy`.

The operator itself, for an arbitrary bounded `P` in place of the interpolation, is
`IntegralOperator.productCLM` of `Numlib/IntegralEquations/ProductIntegration`, and the graded
meshes of §12.5.3 and §12.5.4 are `Numlib/Approximation/GradedMesh`.  What remains here is the
book's numbered results, each a specialization of one of those.

## Main results

* `isCollectivelyCompactFamily_productCLM` — assumptions A1–A3 for the product integration family,
  in the book's form of §12.4.3, so that the framework of that section applies verbatim.  A2 is
  Exercise 12.5.1 and A3 is the compactness half of the proof of Theorem 12.5.1.
* `theorem_12_5_1` — for all large `n` the approximating equations are uniquely solvable with
  uniformly bounded inverses and `‖u - u_n‖_∞ ≤ c ‖K u - K_n u‖_∞`, which is (12.5.17).
* `example_12_5_2` — the product trapezoidal rate (12.5.18),
  `‖u - u_n‖_∞ ≤ (c h²/8) max |∂²(l u)/∂y²|`.
* `lemma_12_5_5` — the interpolation error (12.5.35) `‖u - P_n u‖_∞ ≤ c n^{-(m+1)}` on Rice's
  graded mesh `x_j = (j/n)^q` of (12.5.30), for a function of type `(γ, m + 1)` and `q ≥ (m+1)/γ`.
  The book states the lemma without proof; it is `norm_sub_piecewisePolyInterpCLM_le_graded`.
* `theorem_12_5_6` — the convergence (12.5.41) `‖u - u_n‖_∞ ≤ c n^{-(m+1)}` of graded-mesh
  product integration on the mesh of the paragraph preceding the theorem, graded towards *both*
  endpoints, with the regularity of Theorem 12.5.4 taken as a hypothesis, which is what the book's
  own use of it amounts to.

## Not formalized here

* Theorem 12.5.4, the regularity of the solution of a weakly singular equation.  It is the one
  item of the chapter whose *mathematics*, and not merely whose supporting API, is missing: the
  book proves it by differentiating `u = (f + K u)/λ` under the singular integral sign and
  bootstrapping, and nothing in `Numlib/IntegralEquations/WeaklySingular` touches
  differentiability.  `theorem_12_5_6` therefore takes its conclusion as a hypothesis.
* §12.5.2, the generalizations to kernels not of the form `l g`, and the numerical examples.

## Conventions

As in §12.1 the book's scalar `λ` is written `μ`, and the measure is therefore written `ν`.  The
book's domain is `[a, b]`, which is `IntegralOperator.iccMeasure`; the backbone statements the
results below specialize are for a compact metric space carrying a Borel measure, the generality of
`Numlib/IntegralEquations/WeaklySingular`.  The interpolation `[·]_n` is any sequence of bounded
operators converging pointwise to the identity with uniformly bounded norms; the book's piecewise
linear interpolation is `piecewiseLinearInterpCLM`, whose norm is one.
-/

open Filter Topology

namespace AtkinsonHan.Chapter12

/-! ### The product integration operator -/

section ProductIntegration

open IntegralOperator MeasureTheory

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {ν : Measure X} {g : X × X → ℝ}

/-- **Assumptions A1–A3 for the product integration family** (the proof of Theorem 12.5.1): the
product operators `K_n` built from approximations `P_n` of uniformly bounded norm converging
pointwise to the identity are collectively compact and converge pointwise to the integral operator
of the kernel `l g`.

Boundedness (A1) is carried by the type `C(X, ℝ) →L[ℝ] C(X, ℝ)`; A2 is
`IntegralOperator.tendsto_productCLM` and A3 is
`IntegralOperator.isCollectivelyCompact_productCLM`, the book's form (12.4.53) of the latter being
the backbone's by `isCollectivelyCompactFamily_of_isCollectivelyCompact`. -/
theorem isCollectivelyCompactFamily_productCLM (hg : IsAdmissibleKernel ν g) (l : C(X × X, ℝ))
    {P : ℕ → C(X, ℝ) →L[ℝ] C(X, ℝ)} {Cp : ℝ} (hCp : ∀ n, ‖P n‖ ≤ Cp)
    (hP : ∀ v : C(X, ℝ), Tendsto (fun n => P n v) atTop (𝓝 v)) :
    IsCollectivelyCompactFamily (fun n => productCLM hg l (P n)) (productCLM hg l 1) :=
  isCollectivelyCompactFamily_of_isCollectivelyCompact
    (isCollectivelyCompact_productCLM hg l hCp) fun v => tendsto_productCLM hg l hP v

end ProductIntegration

/-! ### Theorem 12.5.1 -/

section Theorem1

open IntegralOperator MeasureTheory

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {ν : Measure X} {g : X × X → ℝ}

/-- **Theorem 12.5.1, the convergence of product integration.**  Let `g` satisfy the two
weak-singularity conditions (12.5.15)–(12.5.16) — that is, let `g` be an admissible kernel — let
`l` be continuous, and let `K` be the integral operator of `k = l g`.  Let `λ ≠ 0` be such that
`λ - K` is invertible, and let `K_n` be the product rule obtained by replacing `l (x, ·) u (·)` by
`P_n (l (x, ·) u (·))` for a sequence of operators of uniformly bounded norm converging pointwise
to the identity — the piecewise linear interpolants of (12.5.4), for instance.

Then there is a constant `c` such that for all large `n` the operator `λ - K_n` is invertible with
`‖(λ - K_n)⁻¹‖ ≤ c`, so the approximating equations are uniquely solvable, and

`‖u - u_n‖_∞ ≤ c ‖K u - K_n u‖_∞`,   (12.5.17)

the consistency error at the exact solution.

The proof is the book's: `isCollectivelyCompactFamily_productCLM` verifies A1–A3, and the abstract
`exists_norm_inverse_le_of_isCollectivelyCompactFamily` of §12.4.3 — Lemma 12.4.7 followed by
Theorem 12.4.4 — does the rest. -/
theorem theorem_12_5_1 (hg : IsAdmissibleKernel ν g) (l : C(X × X, ℝ))
    {P : ℕ → C(X, ℝ) →L[ℝ] C(X, ℝ)} {Cp : ℝ} (hCp : ∀ n, ‖P n‖ ≤ Cp)
    (hP : ∀ v : C(X, ℝ), Tendsto (fun n => P n v) atTop (𝓝 v))
    {μ : ℝ} (hμ : μ ≠ 0) {e : C(X, ℝ) ≃L[ℝ] C(X, ℝ)}
    (he : (e : C(X, ℝ) →L[ℝ] C(X, ℝ))
      = μ • 1 - admissibleKernelCLM (hg.mul_continuousMap l)) :
    ∃ c : ℝ, ∀ᶠ n in atTop, ∃ en : C(X, ℝ) ≃L[ℝ] C(X, ℝ),
      (en : C(X, ℝ) →L[ℝ] C(X, ℝ)) = μ • 1 - productCLM hg l (P n) ∧
        ‖(en.symm : C(X, ℝ) →L[ℝ] C(X, ℝ))‖ ≤ c ∧
        ∀ f u un : C(X, ℝ),
          (μ • 1 - admissibleKernelCLM (hg.mul_continuousMap l) :
            C(X, ℝ) →L[ℝ] C(X, ℝ)) u = f →
          (μ • 1 - productCLM hg l (P n) : C(X, ℝ) →L[ℝ] C(X, ℝ)) un = f →
          ‖u - un‖ ≤ c * ‖admissibleKernelCLM (hg.mul_continuousMap l) u
            - productCLM hg l (P n) u‖ := by
  have hone := productCLM_one hg l
  have hfam := isCollectivelyCompactFamily_productCLM hg l hCp hP
  rw [hone] at hfam
  exact exists_norm_inverse_le_of_isCollectivelyCompactFamily hμ hfam he

end Theorem1

/-! ### Example 12.5.2: the product trapezoidal rule -/

section Trapezoidal

open IntegralOperator MeasureTheory

variable {a b : ℝ}

/-- **Example 12.5.2, the rate of the product trapezoidal rule (12.5.18).**  Take for `P_n` the
piecewise linear interpolation at the breakpoints of a partition of `[a, b]` whose mesh `h_n` tends
to zero.  Then Theorem 12.5.1 applies — the interpolation operators have norm one and converge
pointwise — and, whenever `y ↦ l (x, y) u (y)` is `C²` with second derivative bounded by `M₂`
uniformly in `x`,

`‖u - u_n‖_∞ ≤ c (h_n²/8) M₂`.

The interpolation error `‖z - P_n z‖ ≤ h² ‖z''‖/8` is `norm_sub_piecewiseLinearInterpCLM_le`, which
`norm_admissibleKernelCLM_sub_productCLM_le` turns into the consistency error `‖K u - K_n u‖`, and
the constant `c` absorbs the uniform bound on `‖(λ - K_n)⁻¹‖` and the row bound `c_g` of the
singular factor. -/
theorem example_12_5_2 {g : Set.Icc a b × Set.Icc a b → ℝ}
    (hg : IsAdmissibleKernel (iccMeasure a b) g) (l : C(Set.Icc a b × Set.Icc a b, ℝ))
    {N : ℕ → ℕ} {y : ℕ → ℕ → Set.Icc a b} {h : ℕ → ℝ}
    (hstep : ∀ n, ∀ i ≤ N n, (y n i : ℝ) < (y n (i + 1) : ℝ))
    (hfirst : ∀ n, (y n 0 : ℝ) = a) (hlast : ∀ n, (y n (N n + 1) : ℝ) = b)
    (hmesh : ∀ n, ∀ i ≤ N n, (y n (i + 1) : ℝ) - (y n i : ℝ) ≤ h n)
    (hh : Tendsto h atTop (𝓝 0)) {μ : ℝ} (hμ : μ ≠ 0)
    {e : C(Set.Icc a b, ℝ) ≃L[ℝ] C(Set.Icc a b, ℝ)}
    (he : (e : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))
      = μ • 1 - admissibleKernelCLM (hg.mul_continuousMap l)) :
    ∃ c : ℝ, ∀ᶠ n in atTop,
      (∀ f : C(Set.Icc a b, ℝ), ∃! un : C(Set.Icc a b, ℝ),
        (μ • 1 - productCLM hg l (piecewiseLinearInterpCLM (N n) (y n)) :
          C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) un = f) ∧
      ∀ (G : Set.Icc a b → ℝ → ℝ) (M₂ : ℝ) (f u un : C(Set.Icc a b, ℝ)),
        (∀ x, ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) (G x)) →
        (∀ x, ∀ t : Set.Icc a b, l (x, t) * u t = G x (t : ℝ)) →
        (∀ x, ∀ t ∈ Set.Icc a b, |iteratedDeriv 2 (G x) t| ≤ M₂) →
        (μ • 1 - admissibleKernelCLM (hg.mul_continuousMap l) :
          C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) u = f →
        (μ • 1 - productCLM hg l (piecewiseLinearInterpCLM (N n) (y n)) :
          C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) un = f →
        ‖u - un‖ ≤ c * (h n ^ 2 / 8 * M₂) := by
  classical
  set P : ℕ → C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ) :=
    fun n => piecewiseLinearInterpCLM (N n) (y n) with hPdef
  have hnormP : ∀ n, ‖P n‖ = 1 := fun n =>
    norm_piecewiseLinearInterpCLM (hstep n) (hfirst n) (hlast n)
  have hCp : ∀ n, ‖P n‖ ≤ 1 := fun n => le_of_eq (hnormP n)
  have hPconv : ∀ v : C(Set.Icc a b, ℝ), Tendsto (fun n => P n v) atTop (𝓝 v) :=
    tendsto_piecewiseLinearInterpCLM hstep hfirst hlast hmesh hh
  obtain ⟨c, hc⟩ := theorem_12_5_1 hg l hCp hPconv hμ he
  refine ⟨c * rowBound (iccMeasure a b) g, ?_⟩
  filter_upwards [hc] with n hn
  obtain ⟨en, hencoe, hennorm, herr⟩ := hn
  have hsolve : ∀ f : C(Set.Icc a b, ℝ), ∃! un : C(Set.Icc a b, ℝ),
      (μ • 1 - productCLM hg l (P n) :
        C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) un = f := fun f => by
    simpa only [← hencoe, ContinuousLinearEquiv.coe_coe] using en.bijective.existsUnique f
  refine ⟨hsolve, fun G M₂ f u un hG hGval hM₂ hu hun => ?_⟩
  -- the consistency error is the interpolation error of `l (x, ·) u (·)`, uniformly in `x`
  have hM0 : (0 : ℝ) ≤ h n ^ 2 / 8 * M₂ := by
    have h1 : (0 : ℝ) ≤ M₂ :=
      le_trans (abs_nonneg _) (hM₂ (y n 0) ((y n 0 : ℝ)) (y n 0).2)
    positivity
  have hcons : ‖admissibleKernelCLM (hg.mul_continuousMap l) u - productCLM hg l (P n) u‖
      ≤ rowBound (iccMeasure a b) g * (h n ^ 2 / 8 * M₂) :=
    norm_admissibleKernelCLM_sub_productCLM_le hg l (P n) u hM0 fun x =>
      norm_sub_piecewiseLinearInterpCLM_le (hstep n) (hfirst n) (hlast n) (hG x)
        (f := prodFactor l x u) (fun t => hGval x t) (hmesh n) (hM₂ x)
  calc ‖u - un‖
      ≤ c * ‖admissibleKernelCLM (hg.mul_continuousMap l) u - productCLM hg l (P n) u‖ :=
        herr f u un hu hun
    _ ≤ c * (rowBound (iccMeasure a b) g * (h n ^ 2 / 8 * M₂)) :=
        mul_le_mul_of_nonneg_left hcons (le_trans (norm_nonneg _) hennorm)
    _ = c * rowBound (iccMeasure a b) g * (h n ^ 2 / 8 * M₂) := by ring

end Trapezoidal

/-! ### Lemma 12.5.5: interpolation on a graded mesh -/

section GradedMesh

/-- **Lemma 12.5.5**, Rice's graded-mesh interpolation error.  For `0 < γ < 1` let `u` be of
Rice's type `(γ, m + 1)` on `[0, 1]` — Hölder continuous with exponent `γ`, of class `C^{m+1}` on
`(0, 1]` and with `|u^{(m+1)}(s)| ≤ c s^{γ - (m+1)}` — and let `P_n` be piecewise polynomial
interpolation of degree `m` on the graded mesh `x_j = (j/n)^q` of (12.5.30), at nodes placed at
fixed fractions `0 = μ_0 < ⋯ < μ_m = 1` of each panel, as in (12.5.31)–(12.5.32).  Then for
`q ≥ (m + 1)/γ`,

`‖u - P_n u‖_∞ ≤ C n^{-(m+1)}`   (12.5.35)

with `C` independent of `n`.

The book states the lemma without proof, citing Rice and Atkinson; the proof is
`norm_sub_piecewisePolyInterpCLM_le_graded` of `Numlib/Approximation/GradedMesh`, of which this is
the verbatim instance. -/
theorem lemma_12_5_5 {m : ℕ} {γ q H c : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hq : ((m : ℝ) + 1) / γ ≤ q) {μ : Fin (m + 1) → ℝ}
    (hμ0 : μ 0 = 0) (hμ1 : μ (Fin.last m) = 1) (hμmono : StrictMono μ)
    {U : ℝ → ℝ} {u : C(Set.Icc (0 : ℝ) 1, ℝ)} (hu : ∀ t : Set.Icc (0 : ℝ) 1, u t = U ((t : ℝ)))
    (hH : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, |U s - U t| ≤ H * |s - t| ^ γ)
    (hUC : ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) U (Set.Ioi 0))
    (hUd : ∀ s ∈ Set.Ioc (0 : ℝ) 1, |iteratedDeriv (m + 1) U s| ≤ c * s ^ (γ - ((m : ℝ) + 1)))
    {x : ℕ → ℕ → Set.Icc (0 : ℝ) 1} {node : ℕ → ℕ → Fin (m + 1) → Set.Icc (0 : ℝ) 1}
    (hx : ∀ N, ∀ j ≤ N + 1, (x N j : ℝ) = ((j : ℝ) / ((N : ℝ) + 1)) ^ q)
    (hnode : ∀ N, ∀ j ≤ N, ∀ i, (node N j i : ℝ)
      = (x N j : ℝ) + μ i * ((x N (j + 1) : ℝ) - (x N j : ℝ))) :
    ∃ C : ℝ, ∀ N : ℕ,
      ‖u - piecewisePolyInterpCLM N m (x N) (node N) u‖ ≤ C / ((N : ℝ) + 1) ^ (m + 1) :=
  norm_sub_piecewisePolyInterpCLM_le_graded hγ0 hγ1 hq hμ0 hμ1 hμmono hu hH hUC hUd hx hnode

end GradedMesh


/-! ### Theorem 12.5.6 -/

section Theorem6

open IntegralOperator MeasureTheory

/-- **Theorem 12.5.6**, the convergence of graded-mesh product integration for a weakly singular
equation.  Let `g` be an admissible (weakly singular) factor, `l` continuous, `λ ≠ 0` with
`λ - K` invertible, and let `K_n` be the product rule (12.5.38) obtained by replacing
`l (x, ·) u (·)` by its piecewise polynomial interpolant of degree `m` on the mesh of the
paragraph preceding the theorem — graded towards both endpoints with exponent `q ≥ (m + 1)/γ`,
`n = 2 (p + 1)` panels.  Assume, as Theorem 12.5.4 gives, that every row function
`y ↦ l (x, y) u (y)` of the exact solution is of Rice's type `(γ, m + 1)` at both endpoints, with
constants independent of `x`.  Then for all large `n` the approximating equations are uniquely
solvable and

`‖u - u_n‖_∞ ≤ c n^{-(m+1)}`   (12.5.41).

The proof is the book's: `theorem_12_5_1` gives `‖u - u_n‖ ≤ c ‖K u - K_n u‖`, the consistency
error is the interpolation error of the row functions integrated against `g`, which is
`norm_admissibleKernelCLM_sub_productCLM_le`, and
`norm_sub_piecewisePolyInterpCLM_le_gradedSym` — Lemma 12.5.5 on the two-sided mesh — bounds
that by `c n^{-(m+1)}` uniformly in the row.  The mesh is `isPanelNodes_gradedSym`, the width of
its panels `sub_le_gradedSym`, and the Lebesgue bound of its nodes
`exists_isPanelLebesgueBound_of_affine`. -/
theorem theorem_12_5_6 {a b : ℝ} (hab : a < b) {m : ℕ} {γ q : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hq : ((m : ℝ) + 1) / γ ≤ q)
    {ν : Fin (m + 1) → ℝ} (hν0 : ν 0 = 0) (hν1 : ν (Fin.last m) = 1) (hνmono : StrictMono ν)
    {x : ℕ → ℕ → Set.Icc a b} {node : ℕ → ℕ → Fin (m + 1) → Set.Icc a b}
    (hxL : ∀ p, ∀ j ≤ p + 1,
      (x p j : ℝ) = a + ((j : ℝ) / ((p + 1 : ℕ) : ℝ)) ^ q * ((b - a) / 2))
    (hxR : ∀ p, ∀ j ≤ p + 1, (x p (2 * (p + 1) - j) : ℝ) = a + b - (x p j : ℝ))
    (hnodeL : ∀ p, ∀ j < p + 1, ∀ i, (node p j i : ℝ)
      = (x p j : ℝ) + ν i * ((x p (j + 1) : ℝ) - (x p j : ℝ)))
    (hnodeR : ∀ p, ∀ j, p + 1 ≤ j → j ≤ 2 * p + 1 → ∀ i, (node p j i : ℝ)
      = (x p j : ℝ) + (1 - ν i.rev) * ((x p (j + 1) : ℝ) - (x p j : ℝ)))
    {g : Set.Icc a b × Set.Icc a b → ℝ} (hg : IsAdmissibleKernel (iccMeasure a b) g)
    (l : C(Set.Icc a b × Set.Icc a b, ℝ)) {lam : ℝ} (hlam : lam ≠ 0)
    {e : C(Set.Icc a b, ℝ) ≃L[ℝ] C(Set.Icc a b, ℝ)}
    (he : (e : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))
      = lam • 1 - admissibleKernelCLM (hg.mul_continuousMap l))
    {f u : C(Set.Icc a b, ℝ)}
    (hu : (lam • 1 - admissibleKernelCLM (hg.mul_continuousMap l) :
      C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) u = f)
    {W : Set.Icc a b → ℝ → ℝ} {H cR : ℝ}
    (hW : ∀ z : Set.Icc a b, ∀ t : Set.Icc a b, prodFactor l z u t = W z ((t : ℝ)))
    (hWH : ∀ z : Set.Icc a b, ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
      |W z s - W z t| ≤ H * |s - t| ^ γ)
    (hWC : ∀ z : Set.Icc a b, ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (W z) (Set.Ioo a b))
    (hWL : ∀ z : Set.Icc a b, ∀ s ∈ Set.Ioc a ((a + b) / 2),
      |iteratedDeriv (m + 1) (W z) s| ≤ cR * (s - a) ^ (γ - ((m : ℝ) + 1)))
    (hWR : ∀ z : Set.Icc a b, ∀ s ∈ Set.Ico ((a + b) / 2) b,
      |iteratedDeriv (m + 1) (W z) s| ≤ cR * (b - s) ^ (γ - ((m : ℝ) + 1))) :
    ∃ C : ℝ, ∀ᶠ p in atTop,
      (∀ h : C(Set.Icc a b, ℝ), ∃! un : C(Set.Icc a b, ℝ),
        (lam • 1 - productCLM hg l (piecewisePolyInterpCLM (2 * p + 1) m (x p) (node p)) :
          C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) un = h) ∧
      ∀ un : C(Set.Icc a b, ℝ),
        (lam • 1 - productCLM hg l (piecewisePolyInterpCLM (2 * p + 1) m (x p) (node p)) :
          C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) un = f →
        ‖u - un‖ ≤ C / (2 * ((p : ℝ) + 1)) ^ (m + 1) := by
  classical
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hq1 : (1 : ℝ) ≤ q := by
    have h2 : (1 : ℝ) < ((m : ℝ) + 1) / γ := by
      rw [lt_div_iff₀ hγ0]
      linarith
    linarith
  have hS0 : (0 : ℝ) < (b - a) / 2 := by linarith
  have hfact0 : (0 : ℝ) < ((m + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (m + 1)
  -- the nodes sit at fixed fractions of every panel — at the reference partition `ν` on the
  -- panels of the left half and at its reflection on those of the right — so a single Lebesgue
  -- bound, depending on `ν` alone, serves every `p`
  have hnodes : ∀ p : ℕ, IsPanelNodes (2 * p + 1) m (x p) (node p) := fun p =>
    isPanelNodes_gradedSym hab (Nat.succ_pos p) (by omega) hq1 hν0 hν1 hνmono (hxL p) (hxR p)
      (hnodeL p) (hnodeR p)
  have hinj : ∀ k : Fin 2, Function.Injective (![ν, fun i => 1 - ν i.rev] k) := by
    intro k
    fin_cases k
    · exact hνmono.injective
    · refine fun i i' hii => Fin.rev_injective (hνmono.injective ?_)
      have hii' : (1 : ℝ) - ν i.rev = 1 - ν i'.rev := hii
      linarith
  obtain ⟨Λ, hΛfam⟩ := exists_isPanelLebesgueBound_of_affine hinj
  have hΛb : ∀ p : ℕ, IsPanelLebesgueBound (2 * p + 1) m (x p) (node p) Λ := by
    intro p
    refine hΛfam (c := fun j => if j < p + 1 then 0 else 1) (hnodes p) fun j hj i => ?_
    by_cases hjr : j < p + 1
    · simp only [hjr, ↓reduceIte]
      exact hnodeL p j hjr i
    · simp only [hjr, ↓reduceIte]
      exact hnodeR p j (by omega) hj i
  -- the mesh tends to zero, so the projections converge pointwise
  have hmesh : ∀ p : ℕ, ∀ j ≤ 2 * p + 1,
      (x p (j + 1) : ℝ) - (x p j : ℝ) ≤ (b - a) / 2 * q / ((p : ℝ) + 1) := by
    intro p
    have h := sub_le_gradedSym (r := p + 1) (N := 2 * p + 1) hab (Nat.succ_pos p) (by omega) hq1
      (hxL p) (hxR p)
    rwa [show ((p + 1 : ℕ) : ℝ) = (p : ℝ) + 1 by push_cast; ring] at h
  have htend : Tendsto (fun p : ℕ => (b - a) / 2 * q / ((p : ℝ) + 1)) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds
      (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hPconv : ∀ v : C(Set.Icc a b, ℝ),
      Tendsto (fun p => piecewisePolyInterpCLM (2 * p + 1) m (x p) (node p) v) atTop (𝓝 v) :=
    fun v => tendsto_piecewisePolyInterpCLM (N := fun p => 2 * p + 1) hnodes hΛb hmesh htend v
  have hnormP : ∀ p : ℕ, ‖piecewisePolyInterpCLM (2 * p + 1) m (x p) (node p)‖ ≤ Λ := fun p =>
    norm_piecewisePolyInterpCLM_le (hnodes p) (hΛb p)
  -- Theorem 12.5.1
  obtain ⟨c₀, hc₀⟩ := theorem_12_5_1 hg l hnormP hPconv hlam he
  set Cst : ℝ := (1 + Λ) * H * ((b - a) / 2) ^ γ
    + cR * ((b - a) / 2) ^ γ * (q * 2 ^ (q - 1)) ^ (m + 1) / (m + 1).factorial with hCstdef
  have hΛ0 : (0 : ℝ) ≤ Λ := (hΛb 0).nonneg (hnodes 0)
  have hSγ0 : (0 : ℝ) ≤ ((b - a) / 2) ^ γ := Real.rpow_nonneg hS0.le γ
  have hH0 : 0 ≤ H := by
    have h := hWH (x 0 0) a ⟨le_rfl, hab.le⟩ b ⟨hab.le, le_rfl⟩
    rw [abs_of_nonpos (by linarith : a - b ≤ 0), neg_sub] at h
    have h2 : (0 : ℝ) < (b - a) ^ γ := Real.rpow_pos_of_pos (by linarith) γ
    by_contra hcon
    push Not at hcon
    have := mul_neg_of_neg_of_pos hcon h2
    linarith [abs_nonneg (W (x 0 0) a - W (x 0 0) b)]
  have hcR0 : 0 ≤ cR := by
    have h := hWL (x 0 0) ((a + b) / 2) ⟨by linarith, le_rfl⟩
    have h2 : (0 : ℝ) < ((a + b) / 2 - a) ^ (γ - ((m : ℝ) + 1)) :=
      Real.rpow_pos_of_pos (by linarith) _
    by_contra hcon
    push Not at hcon
    have := mul_neg_of_neg_of_pos hcon h2
    linarith [abs_nonneg (iteratedDeriv (m + 1) (W (x 0 0)) ((a + b) / 2))]
  have hCst0 : 0 ≤ Cst := by
    rw [hCstdef]
    have h1 : (0 : ℝ) ≤ (1 + Λ) * H * ((b - a) / 2) ^ γ :=
      mul_nonneg (mul_nonneg (by linarith) hH0) hSγ0
    have h2 : (0 : ℝ)
        ≤ cR * ((b - a) / 2) ^ γ * (q * 2 ^ (q - 1)) ^ (m + 1) / (m + 1).factorial :=
      div_nonneg (mul_nonneg (mul_nonneg hcR0 hSγ0) (pow_nonneg (by positivity) _)) hfact0.le
    linarith
  refine ⟨c₀ * rowBound (iccMeasure a b) g * Cst * 2 ^ (m + 1), ?_⟩
  filter_upwards [hc₀] with p hp
  obtain ⟨en, hencoe, hennorm, herr⟩ := hp
  have hsolve : ∀ h : C(Set.Icc a b, ℝ), ∃! un : C(Set.Icc a b, ℝ),
      (lam • 1 - productCLM hg l (piecewisePolyInterpCLM (2 * p + 1) m (x p) (node p)) :
        C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) un = h := fun h => by
    simpa only [← hencoe, ContinuousLinearEquiv.coe_coe] using en.bijective.existsUnique h
  refine ⟨hsolve, fun un hun => ?_⟩
  -- the consistency error is the interpolation error of the rows, uniformly in the row
  have hcast : ((p + 1 : ℕ) : ℝ) = (p : ℝ) + 1 := by push_cast; ring
  have hcons : ‖admissibleKernelCLM (hg.mul_continuousMap l) u
        - productCLM hg l (piecewisePolyInterpCLM (2 * p + 1) m (x p) (node p)) u‖
      ≤ rowBound (iccMeasure a b) g * (Cst / ((p : ℝ) + 1) ^ (m + 1)) :=
    norm_admissibleKernelCLM_sub_productCLM_le hg l _ u
      (div_nonneg hCst0 (by positivity)) fun z => by
      have hint := norm_sub_piecewisePolyInterpCLM_le_gradedSym (r := p + 1) hab
        (Nat.succ_pos p) (by omega) hγ0 hγ1 hq hν0 hν1 hνmono (hxL p) (hxR p) (hnodeL p) (hnodeR p)
        (hΛb p) (hW z) (hWH z) (hWC z) (hWL z) (hWR z)
      rwa [hcast] at hint
  -- assemble
  have hfinal := herr f u un hu hun
  have hpos : (0 : ℝ) < ((p : ℝ) + 1) ^ (m + 1) := by positivity
  have hc₀0 : (0 : ℝ) ≤ c₀ := le_trans (norm_nonneg _) hennorm
  calc ‖u - un‖
      ≤ c₀ * ‖admissibleKernelCLM (hg.mul_continuousMap l) u
          - productCLM hg l (piecewisePolyInterpCLM (2 * p + 1) m (x p) (node p)) u‖ := hfinal
    _ ≤ c₀ * (rowBound (iccMeasure a b) g * (Cst / ((p : ℝ) + 1) ^ (m + 1))) :=
        mul_le_mul_of_nonneg_left hcons hc₀0
    _ = c₀ * rowBound (iccMeasure a b) g * Cst * 2 ^ (m + 1)
          / (2 * ((p : ℝ) + 1)) ^ (m + 1) := by
        rw [mul_pow]
        field_simp

end Theorem6


end AtkinsonHan.Chapter12
