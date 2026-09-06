import Numlib.Approximation.Interpolation
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

Formalized here is §12.2.1, the piecewise linear collocation method: `P_n` is interpolation at the
breakpoints of a partition of `[a, b]`, and both facts come from
`Numlib/Approximation/Interpolation` — `tendsto_piecewiseLinearInterpCLM` for the pointwise
convergence and `norm_sub_piecewiseLinearInterpCLM_le` for the `h² ‖u''‖ / 8` bound.  Nothing about
the mesh is assumed beyond `h_n → 0`; the book's uniform mesh `h = (b - a) / n` is the case
`x_j = a + j h`.

## Main results

* `equation_12_2_5` — for piecewise linear collocation on a sequence of partitions of vanishing
  mesh, `‖K - P_n K‖ → 0`, the collocation equations are uniquely solvable for all large `n`, and
  `‖u - u_n‖_∞ ≤ c h_n² ‖u''‖_∞` for a `C²` solution, with a constant independent of `n`.

## Not formalized here

* §12.2.2, trigonometric collocation (12.2.17)–(12.2.18).  The interpolatory projection onto the
  trigonometric polynomials exists in the backbone (`trigInterpCLM`), but its Lebesgue constant is
  `O(log n)`, so `P_n u → u` fails for a general continuous `u` and Lemma 12.1.4 does not apply.
  The book instead estimates `(I - P_n) k(·, y)` uniformly in `y`, which needs a modulus of
  continuity argument on the kernel and the `O(log n)` bound itself; neither is in the library.
* §12.2.3, piecewise linear Galerkin (12.2.24), and §12.2.4, trigonometric Galerkin (12.2.29).
  Both are `L²(a, b)` statements, and the library has no bridge from `C([a, b], ℝ)` to `L²(a, b)`:
  no orthogonal projection onto the piecewise linear functions, and no density of those in `L²`.
  The argument itself would be the shorter one — an orthogonal projection has norm one for free —
  so this is missing infrastructure, not missing mathematics.

## Conventions

As in §12.1 the book's scalar `λ` is written `μ`, `λ` being Lean's lambda binder.  The book's
partition is indexed by its number of subintervals; here a sequence `y n : ℕ → Icc a b` of nodes
and a count `N n` are given, of which only `y n 0, …, y n (N n + 1)` are used, exactly as
`piecewiseLinearInterpCLM` takes them.
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

end AtkinsonHan.Chapter12
