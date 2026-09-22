import Mathlib.Analysis.Normed.Module.HahnBanach
import Numlib.Analysis.Convex.Continuity
import Numlib.Analysis.Sobolev.Boundary.PolygonTrace
import Numlib.Approximation.SobolevInterpolation
import Numlib.MeasureTheory.Function.LpSpace.Duality
import Numlib.Variational.Inequality.Approximation
import NumlibSurface.AtkinsonHan.Chapter10.Section04
import NumlibSurface.AtkinsonHan.Chapter11.Section03

/-!
# Atkinson–Han §11.4: numerical approximation of elliptic variational inequalities

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §11.4.

The discrete problem (11.4.3) is the *same* predicate as the continuous one (11.3.3) with a
different constraint set, so §11.4 introduces no new notion of discrete solution, and its unique
solvability is Theorem 11.3.1 again.  What the section adds is the analysis of the error:

* `theorem_11_4_1` — convergence of the discrete solutions when the constraint sets `K_h`
  approximate `K`, the general case in which `K_h ⊄ K`;
* `theorem_11_4_2` — Falk's generalized Céa lemma (11.4.7), and `theorem_11_4_2_of_subset` the
  internal-approximation form that follows it;
* `exercise_11_4_2` — convergence of internal approximations, with no weak compactness;
* `exercise_11_4_3` — the a priori bound (11.4.20) for a regularized functional;
* `theorem_11_4_6` — convergence of the method of numerical integration (11.4.25), the one result
  of the section whose discrete functional `j_h` varies with `h`;
* `theorem_11_4_7` — the error bound (11.4.27) when the discrete functional dominates `j`;
* `example_11_4_3` — the obstacle problem discretized with linear elements on a polygon: the
  optimal-order estimate `‖u − u_h‖_{H¹} ≤ c h` from Falk's lemma, with the discrete admissible
  set `discreteObstacleSet` (`K_h ⊄ K`), `Π_h u ∈ K_h` and `max (u_h, ψ) ∈ K`;
* `example_11_4_4` — the friction problem (11.1.13) discretized with linear elements on a polygon,
  the same estimate `‖u − u_h‖_{H¹} ≤ c(u) h` for an *internal* approximation `V_h ⊆ V = H¹(Ω)`:
  here the residual does not vanish and is integrated by parts on the polygon
  (`laplaceForm_sub_load_eq_normalTrace_add`, `abs_residual_le`), which brings in the trace and
  the boundary term `∫_Γ ∂_ν u (γ v_h − γ u) ds`, bounded through the one-dimensional
  interpolation estimate along each side (`norm_traceL_sub_globalInterp_le`).

`residual` is the book's `R(v, w)` of the display preceding (11.4.7), with the functional at the
two arguments kept separate so that the same definition serves the `R_h` of (11.4.27).

## Deviations from the book

* **The estimates are squared.**  Falk's lemma is `(c₀/2) ‖u - u_h‖² ≤ R(v, u_h) + R(v_h, u) +
  (M²/(2c₀)) ‖u - v_h‖²`, which is what its proof establishes; the book's square-rooted form is
  `theorem_11_4_2_of_subset`, with the constant `max (M/c₀) √(2/c₀)` written out.
* **The weak-limit hypotheses of Theorems 11.4.1 and 11.4.6 are indexed by an arbitrary reindexing
  `σ : ℕ → ℕ`**, because the proof runs through `tendsto_of_subseq_tendsto` and so tests the
  hypothesis along a subsequence.  Boundedness of the discrete solutions is not a separate
  hypothesis: it falls out of Falk's lemma at `v = u` together with an affine minorant of `j`.
* **Exercise 11.4.2 asks for the subspaces to be nested.**  "The union of the `V_h` is dense" does
  not by itself produce, for each `n`, a point of `V_h n` near `u`; monotonicity does, and the
  approximating sequence is then the sequence of best approximations, whose errors are antitone.
* **The `liminf` of Theorem 11.4.6 is written as an eventual strict inequality**, `∀ α < j v, the
  values j_h(v_h) are eventually above α`.  Over `ℝ`, `Filter.liminf` of a sequence unbounded below
  is junk rather than `-∞`, so the inequality `liminf j_h(v_h) ≥ j(v)` spelled with it would be a
  different — and, on such a sequence, false — statement; the eventual form is the one the proof
  uses and the one that carries no hidden boundedness.
* **Theorem 11.4.6 drops the hypotheses of it that only make the discrete problem solvable**:
  the finite dimensionality of the `V_h` and the convexity and lower semicontinuity of the `j_h`
  are what Theorem 11.3.1 needs to produce `u_h`, and the theorem takes the `u_h` as given.

* **Example 11.4.3 reads the data on continuous representatives.** The regularity `u, ψ ∈ H²(Ω)`
  of the book enters through representatives continuous up to the boundary (as in Theorem
  10.3.9), the boundary conditions `u = 0`, `ψ ≤ 0` on `Γ` are stated on those representatives (on
  a polygon they do not follow from `u ∈ H¹₀(Ω)`, the domain not being `C¹`), and `−Δu ∈ L²(Ω)` —
  the regularity theorem for the obstacle problem on a `C²` domain
  (`Numlib/Analysis/PDE/Elliptic/Obstacle.lean`) — is the hypothesis `a(u, v) = ∫_Ω g v` for all
  `v ∈ H¹₀(Ω)`. The polygon enters through `Triangulation.FrontierSubsetEdges` (`∂Ω` is a union of
  element edges), and the discrete admissible set asks `v_h ≥ ψ` at every vertex (the boundary
  vertices included, where it holds automatically as `v_h = 0 ≥ ψ`).

## The Lagrange multiplier of the friction problem

* `theorem_11_4_5` — the simplified friction problem (11.4.10) is equivalent to the system
  (11.4.21)–(11.4.22) with a multiplier `λ ∈ Λ = {μ ∈ L^∞(Γ) : |μ| ≤ 1}`, and
  `theorem_11_4_5_unique` — the multiplier is unique; over the boundary interface
  `BoundaryData Ω`, `BoundaryData.TraceFamily` of `Numlib/Analysis/Sobolev/Boundary/Data.lean`
  (a bounded `C¹` domain or a polygon, the book's Lipschitz domain).  The book extends the
  functional `ℓ − a(u, ·)` from `H^{1/2}(Γ)` to `L¹(Γ)` by Hahn–Banach and uses the density of
  `H^{1/2}(Γ)` in `L²(Γ)` for the uniqueness; here the functional is extended from the subspace of
  traces of `L¹(σ)` (`exists_multiplier_of_forall_abs_le`, with the Riesz representation
  `(L¹)' = L^∞` of `Numlib/MeasureTheory/Function/LpSpace/Duality.lean`) and the uniqueness rests
  on the traces of the smooth compactly supported functions
  (`ae_eq_zero_of_integral_contDiff_smul_eq_zero`); no fractional space enters.

## Example 11.4.4 and its hypotheses

The estimate of Example 11.4.4 is stated on a regular family of triangulations of the polygon,
as Example 11.4.3 is, with the book's regularity `u ∈ H²(Ω)`, `u|_{Γᵢ} ∈ H²(Γᵢ)` made explicit
(`U₂ : SobolevEuclidean 2 2 2 Ω`, a representative `ũ` continuous on `Ω̄`, and an element of
`SobolevInterval 2 0 1` for the restriction of `ũ` to each side).  Two hypotheses the book leaves
implicit are named: that every boundary edge of every mesh lies on one of the finitely many sides
of the polygon (`hside` — this is what "polygonal domain" means for the boundary bookkeeping, and
it replaces `Triangulation.FrontierSubsetEdges`, which the proof does not use), and that
`‖∂u/∂ν‖_{L²(Γ)}` and `√(meas Γ)` are bounded uniformly in `h` (`hMν`, `hMσ`) — each mesh carries
its own surface measure `Triangulation.boundaryMeasure`, and for a fixed polygon these are the
same number for every mesh.  For the same reason the friction functional `j` of the variational
inequality is the one built from the mesh's trace family, so the continuous problem is stated per
mesh.

## Not formalized

Exercise 11.4.4 (the proof of Theorem 11.4.5 through the regularization (11.4.14)); the analysis
of (11.4.29), the method of numerical integration for the friction problem, which needs the
quadrature functional `j_h` on the boundary; Exercises 11.4.1 and 11.4.5, which name a domain as
well.
-/

open Filter Set Topology
open scoped InnerProductSpace

namespace AtkinsonHan.Chapter11

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- **The residual of the continuous solution `u`** at the pair `(v, w)`, measured with the
functional `j₁` at the first argument and `j₂` at the second:

  `R(v, w) = (A u, v - w) + j₁(v) - j₂(w) - (f, v - w)`.

The `R` of Atkinson–Han's display preceding (11.4.7) is the case `j₁ = j₂ = j`; the `R_h` of
(11.4.27) is `j₁ = j_h` and `j₂ = j`.  It vanishes identically for a variational *equation* —
`j = 0`, `K` a subspace and `v, w ∈ K` — which is what makes Falk's lemma contain Céa's. -/
def residual (A : V → V) (j₁ j₂ : V → ℝ) (f u v w : V) : ℝ :=
  ⟪A u, v - w⟫_ℝ + j₁ v - j₂ w - ⟪f, v - w⟫_ℝ

section

variable {A : V → V} {c₀ M : ℝ} {j jh : V → ℝ} {f u uh : V} {K Kh : Set V}

/-- The constant `c` of the square-rooted error bounds (11.4.7) and (11.4.27). -/
private noncomputable def falkConst (c₀ M : ℝ) : ℝ := max (M / c₀) (Real.sqrt (2 / c₀))

/-- The constant of the square-rooted error bounds is nonnegative. -/
private theorem falkConst_nonneg (hc₀ : 0 < c₀) (hM : 0 ≤ M) : 0 ≤ falkConst c₀ M :=
  le_max_of_le_left (div_nonneg hM hc₀.le)

/-- The scalar step behind the square-rooted form of Falk's lemma: from
`(c₀/2) e² ≤ R + (M²/(2c₀)) d²` and `0 ≤ e, d` follows `e ≤ c (d + √|R|)`. -/
private theorem norm_le_falkConst (hc₀ : 0 < c₀) (hM : 0 ≤ M) {e d R : ℝ} (he : 0 ≤ e)
    (hd : 0 ≤ d) (h : c₀ / 2 * e ^ 2 ≤ R + M ^ 2 / (2 * c₀) * d ^ 2) :
    e ≤ falkConst c₀ M * (d + Real.sqrt |R|) := by
  have hcM : M / c₀ ≤ falkConst c₀ M := le_max_left _ _
  have hcS : Real.sqrt (2 / c₀) ≤ falkConst c₀ M := le_max_right _ _
  have hS0 : (0 : ℝ) ≤ Real.sqrt (2 / c₀) := Real.sqrt_nonneg _
  have hSsq : Real.sqrt (2 / c₀) ^ 2 = 2 / c₀ := Real.sq_sqrt (by positivity)
  have hR : R ≤ |R| := le_abs_self R
  have hRs : Real.sqrt |R| ^ 2 = |R| := Real.sq_sqrt (abs_nonneg R)
  have hRs0 : (0 : ℝ) ≤ Real.sqrt |R| := Real.sqrt_nonneg _
  have hc : 0 ≤ falkConst c₀ M := falkConst_nonneg hc₀ hM
  -- `e² ≤ (2/c₀) |R| + (M/c₀)² d² ≤ c² (√|R| + d)²`
  have hsq : e ^ 2 ≤ (falkConst c₀ M * (d + Real.sqrt |R|)) ^ 2 := by
    have habs : c₀ / 2 * e ^ 2 ≤ |R| + M ^ 2 / (2 * c₀) * d ^ 2 := by linarith
    have h1 : e ^ 2 ≤ 2 / c₀ * |R| + (M / c₀) ^ 2 * d ^ 2 := by
      have hc0 : c₀ ≠ 0 := ne_of_gt hc₀
      have he2 : (2 / c₀) * (c₀ / 2 * e ^ 2) = e ^ 2 := by field_simp
      have hd2 : (2 / c₀) * (|R| + M ^ 2 / (2 * c₀) * d ^ 2)
          = 2 / c₀ * |R| + (M / c₀) ^ 2 * d ^ 2 := by field_simp
      calc e ^ 2 = (2 / c₀) * (c₀ / 2 * e ^ 2) := he2.symm
        _ ≤ (2 / c₀) * (|R| + M ^ 2 / (2 * c₀) * d ^ 2) :=
            mul_le_mul_of_nonneg_left habs (by positivity)
        _ = _ := hd2
    have h2 : 2 / c₀ * |R| ≤ falkConst c₀ M ^ 2 * Real.sqrt |R| ^ 2 := by
      rw [hRs, ← hSsq]
      exact mul_le_mul_of_nonneg_right (by nlinarith) (abs_nonneg R)
    have h3 : (M / c₀) ^ 2 * d ^ 2 ≤ falkConst c₀ M ^ 2 * d ^ 2 :=
      mul_le_mul_of_nonneg_right (by nlinarith [div_nonneg hM hc₀.le]) (sq_nonneg d)
    nlinarith [mul_nonneg (mul_nonneg hc hc) (mul_nonneg hd hRs0)]
  calc e = Real.sqrt (e ^ 2) := (Real.sqrt_sq he).symm
    _ ≤ Real.sqrt ((falkConst c₀ M * (d + Real.sqrt |R|)) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = falkConst c₀ M * (d + Real.sqrt |R|) :=
        Real.sqrt_sq (mul_nonneg hc (by positivity))

/-! ### Theorem 11.4.1: convergence for approximating constraint sets -/

/-- **Theorem 11.4.1.**  Under the hypotheses of Theorem 11.3.1 — `A` strongly monotone with
constant `c₀ > 0` and Lipschitz with constant `M` — let `j` be convex and continuous on the whole
space (the book's (11.4.2): `j` is the restriction to `K` of such a functional), let `K` be convex
and let `{K_h}` be constraint sets such that

* (a) every `v ∈ K` is the limit of a sequence `v_h ∈ K_h`, and
* (b) a weak limit of elements taken from the `K_h` along any reindexing lies in `K`.

Then the solutions `u_h` of the discrete problems (11.4.3) converge to the solution `u` of
(11.3.3) *in norm*.

Hypothesis (b) is indexed by an arbitrary `σ : ℕ → ℕ` because the proof passes to a subsequence;
for an internal approximation, `K_h ⊆ K`, it is automatic, and the whole weak-compactness step is
unnecessary — that is `exercise_11_4_2`.  The boundedness of the `u_h` that the book obtains
separately is not a hypothesis here: it follows from Falk's lemma tested at `v = u` together with
a continuous affine minorant of `j`. -/
theorem theorem_11_4_1 {Kh : ℕ → Set V} {uh : ℕ → V} (hc₀ : 0 < c₀) (hM : 0 ≤ M)
    (hmono : Chapter05.StronglyMonotoneWith A c₀)
    (hlip : ∀ v₁ v₂ : V, ‖A v₁ - A v₂‖ ≤ M * ‖v₁ - v₂‖) (hKcv : Convex ℝ K)
    (hjcv : ConvexOn ℝ univ j) (hjc : Continuous j)
    (happrox : ∀ v ∈ K, ∃ w : ℕ → V, (∀ n, w n ∈ Kh n) ∧ Tendsto w atTop (𝓝 v))
    (hweak : ∀ (σ : ℕ → ℕ) (v : ℕ → V) (z : V), (∀ k, v k ∈ Kh (σ k)) →
      (∀ y : V, Tendsto (fun k => ⟪v k, y⟫_ℝ) atTop (𝓝 ⟪z, y⟫_ℝ)) → z ∈ K)
    (hu : IsVariationalInequalitySolution A j f K u)
    (huh : ∀ n, IsVariationalInequalitySolution A j f (Kh n) (uh n)) :
    Tendsto uh atTop (𝓝 u) :=
  tendsto_of_isVariationalInequalitySolution hc₀ hmono
    ((Chapter05.lipschitzWith_toNNReal_iff hM).1 hlip) hKcv hjcv hjc happrox hweak hu huh

/-! ### Theorem 11.4.2: Falk's generalized Céa lemma -/

/-- **Theorem 11.4.2, Falk's generalized Céa lemma**, the book's (11.4.7).  With
`R(v, w) = (A u, v - w) + j(v) - j(w) - (f, v - w)` the residual of the continuous solution,

  `(c₀/2) ‖u - u_h‖² ≤ inf_{v ∈ K} R(v, u_h) + inf_{v_h ∈ K_h} [R(v_h, u) + (M²/(2c₀)) ‖u - v_h‖²]`.

The estimate is squared, which is the form its proof establishes: it is pure algebra — the two
variational inequalities added to the strong monotonicity inequality, with the cross term treated
by Cauchy–Schwarz, the Lipschitz bound and Young's inequality.  No closedness, convexity or
topology is used, and `K_h` need not meet `K`.

For a variational *equation* — `K` a subspace, `j = 0`, `K_h ⊆ K` — both residuals vanish and this
is Céa's lemma, which this surface has as `AtkinsonHan.Chapter09.proposition_9_1_3`. -/
theorem theorem_11_4_2 (hc₀ : 0 < c₀) (hM : 0 ≤ M) (hmono : Chapter05.StronglyMonotoneWith A c₀)
    (hlip : ∀ v₁ v₂ : V, ‖A v₁ - A v₂‖ ≤ M * ‖v₁ - v₂‖)
    (hu : IsVariationalInequalitySolution A j f K u)
    (huh : IsVariationalInequalitySolution A j f Kh uh) :
    c₀ / 2 * ‖u - uh‖ ^ 2 ≤ (⨅ v : K, residual A j j f u v uh)
      + ⨅ vh : Kh, (residual A j j f u vh u + M ^ 2 / (2 * c₀) * ‖u - vh‖ ^ 2) := by
  have hKne : Nonempty K := ⟨⟨u, hu.1⟩⟩
  have hKhne : Nonempty Kh := ⟨⟨uh, huh.1⟩⟩
  have hfalk : ∀ (v : K) (vh : Kh), c₀ / 2 * ‖u - uh‖ ^ 2 ≤ residual A j j f u v uh
      + (residual A j j f u vh u + M ^ 2 / (2 * c₀) * ‖u - vh‖ ^ 2) := by
    intro v vh
    have h := norm_sub_le_of_isVariationalInequalitySolution hc₀ hmono
      ((Chapter05.lipschitzWith_toNNReal_iff hM).1 hlip) hu huh v.2 vh.2
    simp only [residual]
    linarith
  have h₁ : ∀ v : K, c₀ / 2 * ‖u - uh‖ ^ 2 - residual A j j f u v uh
      ≤ ⨅ vh : Kh, (residual A j j f u vh u + M ^ 2 / (2 * c₀) * ‖u - vh‖ ^ 2) :=
    fun v => le_ciInf fun vh => by linarith [hfalk v vh]
  have h₂ : c₀ / 2 * ‖u - uh‖ ^ 2
      - ⨅ vh : Kh, (residual A j j f u vh u + M ^ 2 / (2 * c₀) * ‖u - vh‖ ^ 2)
      ≤ ⨅ v : K, residual A j j f u v uh :=
    le_ciInf fun v => by linarith [h₁ v]
  linarith

/-- **Theorem 11.4.2**, the internal-approximation form displayed after it: when `K_h ⊆ K` the
first residual vanishes, at `v = u_h`, and the estimate can be square-rooted to

  `‖u - u_h‖ ≤ c inf_{v_h ∈ K_h} (‖u - v_h‖ + |R(v_h, u)|^{1/2})`,  `c = max (M/c₀) √(2/c₀)`.

The book leaves the constant unnamed; it is written out here because the square root of a sum of
two squares is what fixes it. -/
theorem theorem_11_4_2_of_subset (hc₀ : 0 < c₀) (hM : 0 ≤ M)
    (hmono : Chapter05.StronglyMonotoneWith A c₀)
    (hlip : ∀ v₁ v₂ : V, ‖A v₁ - A v₂‖ ≤ M * ‖v₁ - v₂‖) (hsub : Kh ⊆ K)
    (hu : IsVariationalInequalitySolution A j f K u)
    (huh : IsVariationalInequalitySolution A j f Kh uh) :
    ‖u - uh‖ ≤ max (M / c₀) (Real.sqrt (2 / c₀))
      * ⨅ vh : Kh, (‖u - vh‖ + Real.sqrt |residual A j j f u vh u|) := by
  have hKhne : Nonempty Kh := ⟨⟨uh, huh.1⟩⟩
  rw [show max (M / c₀) (Real.sqrt (2 / c₀)) = falkConst c₀ M from rfl,
    Real.mul_iInf_of_nonneg (falkConst_nonneg hc₀ hM)]
  refine le_ciInf fun vh => norm_le_falkConst hc₀ hM (norm_nonneg _) (norm_nonneg _) ?_
  have h := norm_sub_le_of_isVariationalInequalitySolution_of_subset hc₀
    hmono ((Chapter05.lipschitzWith_toNNReal_iff hM).1 hlip) hu huh
    (hsub huh.1) vh.2
  simp only [residual]
  linarith

/-! ### Exercise 11.4.2: internal approximations converge -/

/-- **Exercise 11.4.2.**  Let `V_h` be a nested family of finite-dimensional subspaces of `V` whose
union is dense, and let `j` be continuous.  Then the solutions `u_h` of the internal problems
(11.4.12) converge in norm to the solution `u` of (11.3.3) over `K = V`.

**No weak compactness is used**: the estimate of `theorem_11_4_2_of_subset` at the best
approximation `w_h` to `u` in `V_h` already tends to zero, because `‖u - w_h‖` does and the
residual is continuous in its first argument.  This, and not Theorem 11.4.1, is the statement a
finite element analysis should cite.

The book says only that the union of the `V_h` is dense; nestedness is added because without it
there need be no point of `V_h n` near `u` for *each* `n`.  With it, the best approximations to
`u` have antitone errors, and density makes them tend to zero. -/
theorem exercise_11_4_2 {Vh : ℕ → Submodule ℝ V} [∀ n, FiniteDimensional ℝ (Vh n)]
    {uh : ℕ → V} (hc₀ : 0 < c₀) (hM : 0 ≤ M) (hmono : Chapter05.StronglyMonotoneWith A c₀)
    (hlip : ∀ v₁ v₂ : V, ‖A v₁ - A v₂‖ ≤ M * ‖v₁ - v₂‖) (hVmono : Monotone Vh)
    (hdense : Dense (⋃ n, (Vh n : Set V))) (hjc : Continuous j)
    (hu : IsVariationalInequalitySolution A j f univ u)
    (huh : ∀ n, IsVariationalInequalitySolution A j f (Vh n : Set V) (uh n)) :
    Tendsto uh atTop (𝓝 u) := by
  -- the best approximations to `u` in the `V_h`
  choose w hw using fun n => exists_isBestApprox_of_finiteDimensional (Vh n) u
  have hwmem : ∀ n, w n ∈ (Vh n : Set V) := fun n => (hw n).1
  have hwlim : Tendsto w atTop (𝓝 u) := by
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun n => norm_nonneg _)
      (fun n => le_of_eq (norm_sub_rev _ _)) ?_)
    refine NormedAddGroup.tendsto_nhds_zero.2 fun ε hε => ?_
    obtain ⟨z, hz, hzd⟩ := Metric.mem_closure_iff.1 (hdense u) ε hε
    obtain ⟨m, hm⟩ := mem_iUnion.1 hz
    refine eventually_atTop.2 ⟨m, fun n hn => ?_⟩
    have hzn : z ∈ (Vh n : Set V) := hVmono hn hm
    calc ‖‖u - w n‖‖ = ‖u - w n‖ := by rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      _ ≤ ‖u - z‖ := (hw n).2 z hzn
      _ < ε := by rwa [dist_eq_norm] at hzd
  exact tendsto_of_isVariationalInequalitySolution_of_subset hc₀ hmono
    ((Chapter05.lipschitzWith_toNNReal_iff hM).1 hlip) (fun n => subset_univ _) hjc.continuousOn hu
    huh hwmem hwlim

/-! ### Exercise 11.4.3: the regularized problem -/

omit [CompleteSpace V] in
/-- **Exercise 11.4.3**, the a priori bound (11.4.20) with `β = 1/2`.  If the regularization
satisfies `|j_ε(v) - j(v)| ≤ c₁ ε` for every `v` — the book's (11.4.32) — then the solution `u_ε`
of the regularized inequality of the second kind is within `√(2 c₁ ε / c₀)` of the solution `u` of
the original one.

The constant is the sharp one: at `v = u_ε` and `v_h = u` the cross term of the core estimate
vanishes, so neither the Lipschitz constant nor Young's inequality enters, and going through
Falk's lemma instead would lose a factor of two. -/
theorem exercise_11_4_3 {jeps : V → ℝ} {c₁ ε : ℝ} {ueps : V} (hc₀ : 0 < c₀)
    (hmono : Chapter05.StronglyMonotoneWith A c₀)
    (hu : IsVariationalInequalitySolution A j f univ u)
    (hueps : IsVariationalInequalitySolution A jeps f univ ueps)
    (hreg : ∀ v : V, |jeps v - j v| ≤ c₁ * ε) : ‖u - ueps‖ ≤ Real.sqrt (2 * c₁ * ε / c₀) :=
  norm_sub_le_of_regularization hc₀ hmono hu hueps hreg

/-! ### Theorem 11.4.6: the method of numerical integration -/

/-- **Theorem 11.4.6**, convergence of the method of numerical integration (11.4.25).  The discrete
problem is posed on the whole finite element space `V_h` and replaces the non-differentiable term
`j` of (11.4.11) by a functional `j_h` obtained from a quadrature rule, so the functional varies
with `h`.  Assume

* `{V_h}` are subspaces carrying maps `r_h : U → V_h` on a dense set `U ⊆ V` with `r_h v → v`;
* the family `{j_h}` is *uniformly proper in h*: there are `ℓ₀ ∈ V'` and `c₁ ∈ ℝ` with
  `ℓ₀(v_h) + c₁ ≤ j_h(v_h)` for every `v_h ∈ V_h` and every `h`;
* `v_h ∈ V_h` with `v_h ⇀ v` implies `liminf j_h(v_h) ≥ j(v)`;
* `j_h(r_h v) → j(v)` for every `v ∈ U`.

Then `‖u - u_h‖ → 0`.

This is `tendsto_of_isVariationalInequalitySolution_of_mosco` at `K = V`: the backbone convergence
theorem for an internal approximation whose functional varies, whose two hypotheses on the family
are the weak `liminf` bound above and the recovery sequences `r_h v`, that is, Mosco convergence
`j_h → j`.  Continuity of `j`, which the backbone theorem uses to pass from the dense set `U` to
`V`, is not an extra hypothesis: `j` is real-valued, convex and lower semicontinuous on a Hilbert
space, and `ConvexOn.continuous_of_lowerSemicontinuous` makes those imply it. -/
theorem theorem_11_4_6 {jh : ℕ → V → ℝ} {uh : ℕ → V} {U : Set V} {Vh : ℕ → Submodule ℝ V}
    {r : ℕ → V → V} (hc₀ : 0 < c₀) (hM : 0 ≤ M) (hmono : Chapter05.StronglyMonotoneWith A c₀)
    (hlip : ∀ v₁ v₂ : V, ‖A v₁ - A v₂‖ ≤ M * ‖v₁ - v₂‖)
    (hjcv : ConvexOn ℝ univ j) (hjlsc : LowerSemicontinuous j)
    (hproper : ∃ (l₀ : V →L[ℝ] ℝ) (c₁ : ℝ), ∀ n, ∀ vh ∈ (Vh n : Set V), l₀ vh + c₁ ≤ jh n vh)
    (hliminf : ∀ (σ : ℕ → ℕ) (vh : ℕ → V) (v : V), (∀ k, vh k ∈ (Vh (σ k) : Set V)) →
      (∀ y : V, Tendsto (fun k => ⟪vh k, y⟫_ℝ) atTop (𝓝 ⟪v, y⟫_ℝ)) →
      ∀ α < j v, ∀ᶠ k in atTop, α < jh (σ k) (vh k))
    (hU : Dense U) (hrmem : ∀ v ∈ U, ∀ n, r n v ∈ (Vh n : Set V))
    (hr : ∀ v ∈ U, Tendsto (fun n => r n v) atTop (𝓝 v))
    (hjr : ∀ v ∈ U, Tendsto (fun n => jh n (r n v)) atTop (𝓝 (j v)))
    (hu : IsVariationalInequalitySolution A j f univ u)
    (huh : ∀ n, IsVariationalInequalitySolution A (jh n) f (Vh n : Set V) (uh n)) :
    Tendsto uh atTop (𝓝 u) :=
  tendsto_of_isVariationalInequalitySolution_of_mosco hc₀ hmono
    ((Chapter05.lipschitzWith_toNNReal_iff hM).1 hlip) convex_univ isClosed_univ hjcv
    (ConvexOn.continuous_of_lowerSemicontinuous hjcv hjlsc) (fun _ => subset_univ _) hproper
    hliminf (fun v _ => hU v)
    (fun v hv => ⟨fun n => r n v, fun n => hrmem v hv n, hr v hv, hjr v hv⟩) hu huh

/-! ### Theorem 11.4.7: a discrete functional dominating `j` -/

/-- **Theorem 11.4.7**, the book's (11.4.27).  A method that replaces the convex term `j` on the
discrete set by a *larger* functional `j_h` — the book's (11.4.26), which the
numerical-integration construction (11.4.28) satisfies — obeys the same error bound with the
residual measured by `j_h`:

  `‖u - u_h‖ ≤ c inf_{v_h ∈ K_h} (‖u - v_h‖ + |R_h(v_h, u)|^{1/2})`,
  `R_h(v_h, u) = (A u, v_h - u) + j_h(v_h) - j(u) - (f, v_h - u)`,

with the same constant `c = max (M/c₀) √(2/c₀)` as `theorem_11_4_2_of_subset`.  The algebra is
Falk's, with the single inequality `j(u_h) ≤ j_h(u_h)` inserted at `v = u_h`. -/
theorem theorem_11_4_7 (hc₀ : 0 < c₀) (hM : 0 ≤ M)
    (hmono : Chapter05.StronglyMonotoneWith A c₀)
    (hlip : ∀ v₁ v₂ : V, ‖A v₁ - A v₂‖ ≤ M * ‖v₁ - v₂‖)
    (hu : IsVariationalInequalitySolution A j f univ u)
    (huh : IsVariationalInequalitySolution A jh f Kh uh) (hjle : ∀ vh ∈ Kh, j vh ≤ jh vh) :
    ‖u - uh‖ ≤ max (M / c₀) (Real.sqrt (2 / c₀))
      * ⨅ vh : Kh, (‖u - vh‖ + Real.sqrt |residual A jh j f u vh u|) := by
  have hKhne : Nonempty Kh := ⟨⟨uh, huh.1⟩⟩
  rw [show max (M / c₀) (Real.sqrt (2 / c₀)) = falkConst c₀ M from rfl,
    Real.mul_iInf_of_nonneg (falkConst_nonneg hc₀ hM)]
  refine le_ciInf fun vh => norm_le_falkConst hc₀ hM (norm_nonneg _) (norm_nonneg _) ?_
  have h := norm_sub_le_of_isVariationalInequalitySolution_of_le hc₀
    hmono ((Chapter05.lipschitzWith_toNNReal_iff hM).1 hlip) hu huh
    (mem_univ uh) (hjle uh huh.1) vh.2
  simp only [residual]
  linarith

end


/-! ### Example 11.4.3: the obstacle problem with linear elements

The finite element approximation of the obstacle problem of Example 11.1.1 on a polygon, with
the discrete admissible set `K_h` of continuous piecewise linear functions dominating the
obstacle at the nodes (`discreteObstacleSet`), and the optimal-order estimate
`‖u − u_h‖_{H¹} ≤ c h` (`example_11_4_3`) from Falk's lemma. The triangulation scaffold is
`Numlib/Geometry/Triangulation.lean`, the interpolation estimates are Theorem 10.3.9 for the
linear element (`Chapter10.theorem_10_3_9_linear`), and the finite element space is
`Triangulation.polySpaceZero`; the ingredients specific to the example are the monotonicity of
the linear interpolant (`globalInterp_linear_mono`), the membership `max (u_h, ψ) ∈ K`
(`exists_max_mem_obstacleSet`) and `Π_h u ∈ K_h` (`exists_globalInterp_mem_discreteObstacleSet`).
-/

section Example1143

open MeasureTheory TopologicalSpace EuclideanSpace
open scoped ENNReal

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

/-- The barycentric coordinates are nonnegative on the closed reference triangle. -/
theorem baryCoord_nonneg {x : 𝔼₂} (hx : x ∈ closure (referenceTriangle : Set 𝔼₂)) (i : Fin 3) :
    0 ≤ baryCoord i x := by
  rw [closure_referenceTriangle_eq] at hx
  obtain ⟨h0, h1, h2⟩ := hx
  fin_cases i
  · simp only [baryCoord, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    linarith
  · simpa [baryCoord] using h0
  · simpa [baryCoord] using h1

/-- The barycentric coordinates are polynomials of total degree at most `1`. -/
theorem baryCoord_eq_eval (i : Fin 3) : ∃ q : MvPolynomial (Fin 2) ℝ, q.totalDegree ≤ 1 ∧
    ∀ x : 𝔼₂, baryCoord i x = MvPolynomial.eval (fun j ↦ x j) q := by
  fin_cases i
  · refine ⟨MvPolynomial.C 1 - MvPolynomial.X 0 - MvPolynomial.X 1, ?_, fun x ↦ ?_⟩
    · refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
      · refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
        · simp
        · exact (MvPolynomial.totalDegree_X _).le
      · exact (MvPolynomial.totalDegree_X _).le
    · simp [baryCoord]
  · refine ⟨MvPolynomial.X 0, (MvPolynomial.totalDegree_X _).le, fun x ↦ ?_⟩
    simp [baryCoord]
  · refine ⟨MvPolynomial.X 1, (MvPolynomial.totalDegree_X _).le, fun x ↦ ?_⟩
    simp [baryCoord]

/-- **The linear element is edge unisolvent**: the interpolant is affine along a reference edge
and vanishes at its two ends, which are nodes. -/
theorem isEdgeUnisolvent_linear : IsEdgeUnisolvent referenceTriangleVertex baryCoord := by
  intro a b hab v hv y hy
  rw [segment_eq_image'] at hy
  obtain ⟨s, -, rfl⟩ := hy
  have hlin : ∀ (P Q : 𝔼₂) (t : ℝ),
      Approximation.nodalInterp referenceTriangleVertex baryCoord v (P + t • (Q - P))
        = Approximation.nodalInterp referenceTriangleVertex baryCoord v P
          + t * (Approximation.nodalInterp referenceTriangleVertex baryCoord v Q
            - Approximation.nodalInterp referenceTriangleVertex baryCoord v P) := by
    intro P Q t
    simp only [Approximation.nodalInterp_apply, baryCoord_lineMap, smul_eq_mul, add_mul, sub_mul,
      mul_assoc, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hnode : ∀ c : Fin 3, c ∈ ({a, b} : Set (Fin 3)) →
      Approximation.nodalInterp referenceTriangleVertex baryCoord v (referenceTriangleVertex c)
        = 0 := by
    intro c hc
    rw [isNodalBasis_baryCoord.nodalInterp_apply_node]
    refine hv c ?_
    rcases hc with rfl | rfl
    · exact left_mem_segment ℝ _ _
    · exact right_mem_segment ℝ _ _
  rw [hlin, hnode a (by simp), hnode b (by simp)]
  ring

/-- **The linear interpolant is monotone**: if `v ≤ w` at every vertex then `Π_h v ≤ Π_h w` on
`Ω̄`, the barycentric coordinates being nonnegative on the closed elements. -/
theorem globalInterp_linear_mono {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω) {v w : 𝔼₂ → ℝ}
    (hvw : ∀ x ∈ 𝒯.vertices, v x ≤ w x) {x : 𝔼₂} (hx : x ∈ closure (Ω : Set 𝔼₂)) :
    𝒯.globalInterp referenceTriangleVertex baryCoord v x
      ≤ 𝒯.globalInterp referenceTriangleVertex baryCoord w x := by
  rw [𝒯.closure_eq_iUnion_closedK, mem_iUnion] at hx
  obtain ⟨T, hxT⟩ := hx
  have hxT' := hxT
  rw [← 𝒯.image_closedReferenceTriangle] at hxT'
  obtain ⟨z, hz, rfl⟩ := hxT'
  rw [𝒯.globalInterp_eq_of_mem_closedK _ _ 𝒯.isConformingElement_linear T v hxT,
    𝒯.globalInterp_eq_of_mem_closedK _ _ 𝒯.isConformingElement_linear T w hxT]
  simp only [Triangulation.localInterp_apply, 𝒯.affine_referenceTriangleVertex, 𝒯.affine_symm]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  refine mul_le_mul_of_nonneg_left (hvw _ (𝒯.vertex_mem_vertices T i)) ?_
  refine baryCoord_nonneg ?_ i
  rw [closure_referenceTriangle_eq]
  exact hz

/-- Two functions continuous on `Ω̄` with `v ≤ w` almost everywhere on `Ω` satisfy `v ≤ w` on
`Ω̄`. -/
theorem le_on_closure_of_ae_le {Ω : Opens 𝔼₂} {v w : 𝔼₂ → ℝ}
    (h : ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼₂)), v x ≤ w x)
    (hv : ContinuousOn v (closure (Ω : Set 𝔼₂))) (hw : ContinuousOn w (closure (Ω : Set 𝔼₂))) :
    ∀ x ∈ closure (Ω : Set 𝔼₂), v x ≤ w x := by
  have hmax : EqOn (fun x ↦ max (v x) (w x)) w (closure (Ω : Set 𝔼₂)) := by
    refine Triangulation.eqOn_closure_of_ae_eq ?_ (hv.sup hw) hw
    filter_upwards [h] with x hx
    exact max_eq_right hx
  intro x hx
  have := hmax hx
  simp only at this
  rw [← this]
  exact le_max_left _ _

/-- The `L²(Ω)` norm is at most the tensor Sobolev norm of order `0`. -/
theorem eLpNorm_le_sobolevNorm_zero {Ω : Opens 𝔼₂} {f : 𝔼₂ → ℝ}
    (hf : MemSobolev f 0 2 Ω volume) :
    eLpNorm f 2 (volume.restrict (Ω : Set 𝔼₂)) ≤ sobolevNorm f 0 2 Ω volume := by
  have hW := hasWeakIteratedFDerivOn_zero (μ := volume) (hf.memLp.locallyIntegrableOn one_le_two)
  have hae : ∀ᵐ x ∂volume.restrict (Ω : Set 𝔼₂),
      ‖weakIteratedFDeriv 0 f Ω volume x‖ = ‖f x‖ := by
    filter_upwards [(ae_restrict_iff' Ω.isOpen.measurableSet).2 hW.weakIteratedFDeriv_ae_eq]
      with x hx
    rw [hx]
    exact LinearIsometryEquiv.norm_map _ _
  rw [← eLpNorm_congr_norm_ae (hf.memLp_weakIteratedFDeriv le_rfl).aestronglyMeasurable
    hf.memLp.aestronglyMeasurable hae]
  exact eLpNorm_weakIteratedFDeriv_le_sobolevNorm one_le_two (by simp) le_rfl


/-- **The discrete admissible set `K_h`** of Example 11.4.3 for the linear element on a
triangulation `𝒯_h`: the continuous piecewise linear functions `v_h ∈ H¹₀(Ω)` (the elements of
`Triangulation.polySpaceZero 2 1`, through a representative `v` continuous on `Ω̄`, piecewise
linear, vanishing on `∂Ω`) with `v_h(x) ≥ ψ(x)` at every node `x`, the obstacle `ψ` being read
on a representative `ψ'`. In general `K_h ⊄ K`. -/
def discreteObstacleSet {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω) (ψ' : 𝔼₂ → ℝ) :
    Set (SobolevEuclideanZero 2 1 2 Ω) :=
  {vh | ∃ v : 𝔼₂ → ℝ, ContinuousOn v (closure (Ω : Set 𝔼₂)) ∧ 𝒯.IsPiecewisePoly 1 v ∧
    EqOn v 0 (frontier (Ω : Set 𝔼₂)) ∧
    SobolevMultiIndex.fn (vh : SobolevEuclidean 2 1 2 Ω) =ᵐ[volume.restrict (Ω : Set 𝔼₂)] v ∧
    ∀ x ∈ 𝒯.vertices, ψ' x ≤ v x}

/-- `K_h` lies in the finite element space `V_h` of continuous piecewise linear functions
vanishing on `∂Ω`. -/
theorem discreteObstacleSet_subset {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω) (ψ' : 𝔼₂ → ℝ) :
    discreteObstacleSet 𝒯 ψ' ⊆ (𝒯.polySpaceZero 2 1 : Set (SobolevEuclideanZero 2 1 2 Ω)) := by
  rintro vh ⟨v, hvc, hvp, hv0, hvh, -⟩
  exact ⟨v, hvc, hvp, hv0, hvh⟩

/-- **`u^{h,*} = max (u_h, ψ)` lies in `K`**: for `u_h ∈ H¹₀(Ω)` with a representative continuous
on `Ω̄`, in `H¹(Ω)` and vanishing on `∂Ω`, and an obstacle `ψ ∈ H¹(Ω)` with a representative
continuous on `Ω̄` and `≤ 0` on `∂Ω`, the function `max (u_h, ψ)` is the function of an element
of the admissible set `K = {v ∈ H¹₀(Ω) : v ≥ ψ}`: it is `u_h + (ψ − u_h)⁺ ∈ H¹(Ω)`, continuous on
`Ω̄` and vanishing on `∂Ω`, hence in `H¹₀(Ω)` (Theorem 9.17, (i) ⇒ (ii)). -/
theorem exists_max_mem_obstacleSet {Ω : Opens 𝔼₂} {ψ : SobolevEuclidean 2 1 2 Ω} {ψ' : 𝔼₂ → ℝ}
    (hψ : SobolevMultiIndex.fn ψ =ᵐ[volume.restrict (Ω : Set 𝔼₂)] ψ')
    (hψc : ContinuousOn ψ' (closure (Ω : Set 𝔼₂))) (hψ1 : MemSobolev ψ' 1 2 Ω volume)
    (hψ0 : ∀ x ∈ frontier (Ω : Set 𝔼₂), ψ' x ≤ 0)
    {v : 𝔼₂ → ℝ} (hvc : ContinuousOn v (closure (Ω : Set 𝔼₂))) (hv1 : MemSobolev v 1 2 Ω volume)
    (hv0 : EqOn v 0 (frontier (Ω : Set 𝔼₂))) :
    ∃ w : SobolevEuclideanZero 2 1 2 Ω, w ∈ obstacleSet (d := 1) Ω ψ ∧
      SobolevMultiIndex.fn (w : SobolevEuclidean 2 1 2 Ω) =ᵐ[volume.restrict (Ω : Set 𝔼₂)]
        fun x ↦ max (v x) (ψ' x) := by
  have hmax : ∀ x, v x + max (ψ' x - v x) 0 = max (v x) (ψ' x) := fun x ↦ by
    rcases le_total (v x) (ψ' x) with h | h
    · rw [max_eq_left (sub_nonneg.2 h), max_eq_right h]
      ring
    · rw [max_eq_right (sub_nonpos.2 h), max_eq_left h, add_zero]
  -- `max (v, ψ') = v + (ψ' − v)⁺ ∈ H¹(Ω)`
  have hmem : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (fun x ↦ max (v x) (ψ' x)) 1 2 Ω volume := by
    have h1 := hv1.memSobolevMultiIndex (b := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis)
    have h2 := ((hψ1.sub hv1).memSobolevMultiIndex
      (b := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis)).posPart one_le_two
    have h3 := h1.add h2
    refine h3.congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    exact hmax x
  have hex := hmem.exists_sobolevMultiIndex
  obtain ⟨w', hw'⟩ := hex
  have hcont : ContinuousOn (fun x ↦ max (v x) (ψ' x)) (closure (Ω : Set 𝔼₂)) := hvc.sup hψc
  have h0 : EqOn (fun x ↦ max (v x) (ψ' x)) 0 (frontier (Ω : Set 𝔼₂)) := fun x hx ↦ by
    simp only [hv0 hx, Pi.zero_apply]
    exact max_eq_left (hψ0 x hx)
  have hw'0 : w' ∈ SobolevEuclideanZero 2 1 2 Ω :=
    SobolevEuclideanZero.mem_of_continuousOn_closure_of_eqOn_frontier (by simp) w' hw' hcont h0
  refine ⟨⟨w', hw'0⟩, ?_, hw'⟩
  rw [mem_obstacleSet_iff]
  filter_upwards [hψ, hw'] with x h1 h2
  rw [h1]
  exact (le_max_right _ _).trans_eq h2.symm

/-- The interpolant `Π_h u` of the solution lies in `K_h`: it is a continuous piecewise linear
function vanishing on `∂Ω` with `u` (`Triangulation.globalInterp_eqOn_frontier`), and at every
node it takes the value `u(x) ≥ ψ(x)`. -/
theorem exists_globalInterp_mem_discreteObstacleSet {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω)
    (hedge : 𝒯.FrontierSubsetEdges) {ψ' u' : 𝔼₂ → ℝ}
    (hψu : ∀ x ∈ closure (Ω : Set 𝔼₂), ψ' x ≤ u' x) (hu0 : EqOn u' 0 (frontier (Ω : Set 𝔼₂))) :
    ∃ vh ∈ discreteObstacleSet 𝒯 ψ',
      SobolevMultiIndex.fn (vh : SobolevEuclidean 2 1 2 Ω) =ᵐ[volume.restrict (Ω : Set 𝔼₂)]
        𝒯.globalInterp referenceTriangleVertex baryCoord u' := by
  have hcont := 𝒯.continuousOn_globalInterp referenceTriangleVertex baryCoord
    𝒯.isConformingElement_linear (fun i ↦ (contDiff_baryCoord i).continuous) u'
  have hpoly := 𝒯.globalInterp_isPiecewisePoly 𝒯.isConformingElement_linear baryCoord_eq_eval u'
  have h0 := 𝒯.globalInterp_eqOn_frontier referenceTriangleVertex baryCoord hedge
    𝒯.isConformingElement_linear isEdgeUnisolvent_linear hu0
  have hex := 𝒯.exists_mem_polySpaceZero 2 (by simp) hcont hpoly h0
  obtain ⟨w, -, hw⟩ := hex
  refine ⟨w, ⟨_, hcont, hpoly, h0, hw, fun x hx ↦ ?_⟩, hw⟩
  obtain ⟨T, a, rfl⟩ := 𝒯.exists_vertex_of_mem_vertices hx
  rw [𝒯.globalInterp_eq_of_mem_closedK _ _ 𝒯.isConformingElement_linear T u'
    (𝒯.vertex_mem_closedK T a), 𝒯.localInterp_linear_vertex]
  exact hψu _ (𝒯.closedK_subset_closure T (𝒯.vertex_mem_closedK T a))


/-- The residual of the obstacle problem's solution in terms of `−Δu`: when
`a(u, v) = ∫_Ω g v` for all `v ∈ H¹₀(Ω)` (`g = −Δu ∈ L²(Ω)`), the residual
`R(v, w) = a(u, v − w) − ℓ(v − w)` is `∫_Ω (g − f)(v − w)`, bounded by
`‖g − f‖_{L²} ‖v − w‖_{L²}`. -/
theorem residual_le_of_eq_load {Ω : Opens 𝔼₂}
    (f g : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼₂))) {u : SobolevEuclideanZero 2 1 2 Ω}
    (hΔ : ∀ v : SobolevEuclideanZero 2 1 2 Ω,
      dirichletBilinForm (d := 1) Ω u v = loadZero (d := 1) Ω g v)
    (z : SobolevEuclideanZero 2 1 2 Ω) :
    dirichletBilinForm (d := 1) Ω u z - loadZero (d := 1) Ω f z
      ≤ ‖g - f‖ * (eLpNorm (SobolevMultiIndex.fn (z : SobolevEuclidean 2 1 2 Ω)) 2
        (volume.restrict (Ω : Set 𝔼₂))).toReal := by
  rw [hΔ z, ← sub_apply, ← loadZero_sub]
  refine (le_abs_self _).trans ((Elliptic.abs_load_le Ω (g - f) z).trans_eq ?_)
  rw [Lp.norm_def]
  rfl

/-- Real form of an `ℝ≥0∞` bound `a ≤ ofReal c * S`. -/
theorem toReal_le_of_le_ofReal_mul {a S : ℝ≥0∞} {c : ℝ} (hc : 0 ≤ c) (hS : S ≠ ⊤)
    (h : a ≤ ENNReal.ofReal c * S) : a.toReal ≤ c * S.toReal := by
  have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS) h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] at h'

/-- `v − Π_h v ∈ L²(Ω)` for `v ∈ H²(Ω)` and the linear interpolant. -/
theorem memSobolev_sub_globalInterp_linear {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω) {v : 𝔼₂ → ℝ}
    (hv : MemSobolev v 2 2 Ω volume) :
    MemSobolev (v - 𝒯.globalInterp referenceTriangleVertex baryCoord v) 0 2 Ω volume :=
  (hv.mono_order (by norm_num)).sub
    ((𝒯.memSobolev_globalInterp referenceTriangleVertex baryCoord 𝒯.isConformingElement_linear
      (fun j ↦ (contDiff_baryCoord j).of_le (by simp)) v 2).mono_order (by norm_num))

/-- **`‖max (u_h, ψ) − u_h‖₀ ≤ ‖ψ − Π_h ψ‖₀`** for a continuous piecewise linear `u_h` with
`u_h ≥ ψ` at the vertices: `u_h = Π_h u_h ≥ Π_h ψ` on `Ω̄` by the monotonicity of the linear
interpolant, so that `0 ≤ ψ − u_h ≤ ψ − Π_h ψ` where `u_h < ψ`, and `max (u_h, ψ) − u_h = 0`
elsewhere. -/
theorem eLpNorm_max_sub_le {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω) {ψ' v : 𝔼₂ → ℝ}
    (hψc : ContinuousOn ψ' (closure (Ω : Set 𝔼₂))) (hvc : ContinuousOn v (closure (Ω : Set 𝔼₂)))
    (hvp : 𝒯.IsPiecewisePoly 1 v) (hψv : ∀ x ∈ 𝒯.vertices, ψ' x ≤ v x) :
    eLpNorm (fun x ↦ max (v x) (ψ' x) - v x) 2 (volume.restrict (Ω : Set 𝔼₂))
      ≤ eLpNorm (ψ' - 𝒯.globalInterp referenceTriangleVertex baryCoord ψ') 2
        (volume.restrict (Ω : Set 𝔼₂)) := by
  have hrep : EqOn (𝒯.globalInterp referenceTriangleVertex baryCoord v) v
      (closure (Ω : Set 𝔼₂)) :=
    𝒯.globalInterp_eqOn_closure_of_isPiecewisePoly 𝒯.isConformingElement_linear
      referenceTriangleVertex_mem_closure (fun q hq x ↦ Chapter10.nodalInterp_baryCoord_eval q hq x)
      hvp
  have hge : ∀ x ∈ closure (Ω : Set 𝔼₂),
      𝒯.globalInterp referenceTriangleVertex baryCoord ψ' x ≤ v x := fun x hx ↦
    (globalInterp_linear_mono 𝒯 hψv hx).trans_eq (hrep hx)
  have hpt : ∀ x ∈ (Ω : Set 𝔼₂), ‖max (v x) (ψ' x) - v x‖
      ≤ ‖(ψ' - 𝒯.globalInterp referenceTriangleVertex baryCoord ψ') x‖ := by
    intro x hx
    have h1 := hge x (subset_closure hx)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Pi.sub_apply]
    rcases le_total (ψ' x) (v x) with h | h
    · rw [max_eq_left h, sub_self, abs_zero]
      exact abs_nonneg _
    · rw [max_eq_right h, abs_of_nonneg (sub_nonneg.2 h)]
      exact (sub_le_sub_left h1 _).trans (le_abs_self _)
  have hmeas : AEStronglyMeasurable (fun x ↦ max (v x) (ψ' x) - v x)
      (volume.restrict (Ω : Set 𝔼₂)) := by
    have hv' := (hvc.mono subset_closure).aestronglyMeasurable (μ := volume) Ω.isOpen.measurableSet
    have hψ' := (hψc.mono subset_closure).aestronglyMeasurable (μ := volume) Ω.isOpen.measurableSet
    exact (hv'.sup hψ').sub hv'
  exact eLpNorm_mono_ae hmeas
    ((ae_restrict_iff' Ω.isOpen.measurableSet).2 (Filter.Eventually.of_forall hpt))

/-- **Example 11.4.3.** Theorem 11.4.2 applied to the obstacle problem (Example 11.1.1,
Example 11.3.10) on a polygon `Ω ⊆ B(0, R)` (`∂Ω` a union of element edges), discretized with
linear elements on a regular family of triangulations `{𝒯_h}` with the discrete admissible set
`K_h = {v_h ∈ V_h : v_h(x) ≥ ψ(x) at every node x}` (`discreteObstacleSet`), which is not
contained in `K`. Let `f ∈ L²(Ω)`, let the obstacle `ψ ∈ H¹(Ω)` have a representative `ψ'`
continuous on `Ω̄`, in `H²(Ω)`, with `ψ' ≤ 0` on `∂Ω`, let `u ∈ K` be the solution of the obstacle
problem with a representative `u'` continuous on `Ω̄`, in `H²(Ω)`, vanishing on `∂Ω`, and with
`−Δu = g ∈ L²(Ω)` in the weak sense `a(u, v) = ∫_Ω g v` for `v ∈ H¹₀(Ω)` (the book's
`u ∈ H²(Ω)`; on a `C²` domain this is the regularity theorem for the obstacle problem, on a
polygon it is a hypothesis), and let `u_h ∈ K_h` be the discrete solutions. Then

  `‖u − u_h‖_{H¹(Ω)} ≤ c h`

for a constant `c` depending on `|u|_{2,Ω}`, `|ψ|_{2,Ω}`, `‖f‖₀` and `‖−Δu‖₀` only. The proof is
the book's: Falk's lemma (11.4.7) (`norm_sub_le_of_isVariationalInequalitySolution`, the
pointwise form behind `theorem_11_4_2`) with `v_h = Π_h u ∈ K_h`
(`exists_globalInterp_mem_discreteObstacleSet`) and `v = u^{h,*} = max (u_h, ψ) ∈ K`
(`exists_max_mem_obstacleSet`); the residual is `∫_Ω (−Δu − f)(v − w)` (`residual_le_of_eq_load`),
bounded through the `L²` norms; `‖u − Π_h u‖_{m,Ω} ≤ c h^{2−m} |u|_{2,Ω}` at `m = 0, 1`
(`Chapter10.theorem_10_3_9_linear`); and `‖u^{h,*} − u_h‖₀ ≤ ‖ψ − Π_h ψ‖₀ ≤ c h² |ψ|_{2,Ω}`
(`eLpNorm_max_sub_le`). -/
theorem example_11_4_3 {Ω : Opens 𝔼₂} {ι : Type*} {l : Filter ι} {𝒯 : ι → Triangulation Ω}
    (hreg : Chapter10.IsRegularFamily l fun i ↦ Set.range (𝒯 i).K)
    {H : ℝ} (hH : ∀ i, (𝒯 i).meshSize ≤ H) (hedge : ∀ i, (𝒯 i).FrontierSubsetEdges)
    {R : ℝ} (hR : 0 ≤ R) (hΩ : (Ω : Set 𝔼₂) ⊆ Metric.ball 0 R)
    (f g : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼₂))) {ψ : SobolevEuclidean 2 1 2 Ω} {ψ' : 𝔼₂ → ℝ}
    (hψ : SobolevMultiIndex.fn ψ =ᵐ[volume.restrict (Ω : Set 𝔼₂)] ψ')
    (hψc : ContinuousOn ψ' (closure (Ω : Set 𝔼₂))) (hψ2 : MemSobolev ψ' 2 2 Ω volume)
    (hψ0 : ∀ x ∈ frontier (Ω : Set 𝔼₂), ψ' x ≤ 0)
    {u : SobolevEuclideanZero 2 1 2 Ω}
    (hu : u ∈ obstacleSet (d := 1) Ω ψ ∧ ∀ v ∈ obstacleSet (d := 1) Ω ψ,
      dirichletBilinForm (d := 1) Ω u (v - u) ≥ loadZero (d := 1) Ω f (v - u))
    {u' : 𝔼₂ → ℝ} (hu' : SobolevMultiIndex.fn (u : SobolevEuclidean 2 1 2 Ω)
      =ᵐ[volume.restrict (Ω : Set 𝔼₂)] u')
    (hu'2 : MemSobolev u' 2 2 Ω volume) (hu'c : ContinuousOn u' (closure (Ω : Set 𝔼₂)))
    (hu'0 : EqOn u' 0 (frontier (Ω : Set 𝔼₂)))
    (hΔ : ∀ v : SobolevEuclideanZero 2 1 2 Ω,
      dirichletBilinForm (d := 1) Ω u v = loadZero (d := 1) Ω g v)
    {uh : ι → SobolevEuclideanZero 2 1 2 Ω}
    (huh : ∀ i, uh i ∈ discreteObstacleSet (𝒯 i) ψ' ∧ ∀ vh ∈ discreteObstacleSet (𝒯 i) ψ',
      dirichletBilinForm (d := 1) Ω (uh i) (vh - uh i) ≥ loadZero (d := 1) Ω f (vh - uh i)) :
    ∃ c : ℝ, ∀ i, ‖u - uh i‖ ≤ c * (𝒯 i).meshSize := by
  have hM := dirichletBilinForm_isBoundedWith (d := 1) Ω
  have hα := dirichletBilinForm_isEllipticWith (d := 1) Ω hR hΩ
  have hc₀ : (0 : ℝ) < (1 + (2 * R) ^ 2)⁻¹ := by positivity
  -- the variational inequalities in operator form
  have hmono := Chapter08.stronglyMonotone_toOperator hM hα
  have hlip := Chapter08.lipschitzWith_toOperator zero_le_one hM
  have huVI : IsVariationalInequalitySolution
      (BilinForm.toOperator (dirichletBilinForm (d := 1) Ω) hM) (fun _ ↦ (0 : ℝ))
      (SesqForm.rieszRep (loadZero (d := 1) Ω f)) (obstacleSet (d := 1) Ω ψ) u := by
    rw [Chapter11.isVariationalInequalitySolution_toOperator_iff]
    simpa only [add_zero, sub_zero] using hu
  -- the interpolation estimates of Theorem 10.3.9 for the linear element
  have h1 := Chapter10.theorem_10_3_9_linear (m := 1) le_rfl hreg hH
  obtain ⟨c₁, hc₁, hest₁⟩ := h1
  have h0 := Chapter10.theorem_10_3_9_linear (m := 0) (by norm_num) hreg hH
  obtain ⟨c₀', hc₀', hest₀⟩ := h0
  have hCC := Chapter10.exists_norm_le_sobolevNorm Ω
  obtain ⟨C, hC0, hC⟩ := hCC
  -- the seminorms of the data
  obtain ⟨Su, hSu⟩ : ∃ Su : ℝ, Su = (sobolevSeminorm u' 2 2 Ω volume).toReal := ⟨_, rfl⟩
  obtain ⟨Sψ, hSψ⟩ : ∃ Sψ : ℝ, Sψ = (sobolevSeminorm ψ' 2 2 Ω volume).toReal := ⟨_, rfl⟩
  have hSu0 : 0 ≤ Su := hSu ▸ ENNReal.toReal_nonneg
  have hSψ0 : 0 ≤ Sψ := hSψ ▸ ENNReal.toReal_nonneg
  have hSufin : sobolevSeminorm u' 2 2 Ω volume ≠ ⊤ := hu'2.sobolevSeminorm_ne_top
  have hSψfin : sobolevSeminorm ψ' 2 2 Ω volume ≠ ⊤ := hψ2.sobolevSeminorm_ne_top
  -- the constant
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = ‖g - f‖ * (c₀' * Sψ) + ‖g - f‖ * (c₀' * Su)
      + 1 ^ 2 / (2 * (1 + (2 * R) ^ 2)⁻¹) * (C * (c₁ * Su)) ^ 2 := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine ⟨Real.sqrt (2 / (1 + (2 * R) ^ 2)⁻¹ * K), fun i ↦ ?_⟩
  have hh0 : 0 ≤ (𝒯 i).meshSize := (𝒯 i).meshSize_nonneg
  -- the discrete solution and its representative
  obtain ⟨hmem, hvi⟩ := huh i
  obtain ⟨v, hvc, hvp, hv0, hvh, hψv⟩ := hmem
  have hv1 : MemSobolev v 1 2 Ω volume := hvp.memSobolev hvc 2
  have huhVI : IsVariationalInequalitySolution
      (BilinForm.toOperator (dirichletBilinForm (d := 1) Ω) hM) (fun _ ↦ (0 : ℝ))
      (SesqForm.rieszRep (loadZero (d := 1) Ω f)) (discreteObstacleSet (𝒯 i) ψ') (uh i) := by
    rw [Chapter11.isVariationalInequalitySolution_toOperator_iff]
    simpa only [add_zero, sub_zero] using huh i
  -- `ψ ≤ u` on `Ω̄`
  have hψu : ∀ x ∈ closure (Ω : Set 𝔼₂), ψ' x ≤ u' x := by
    refine le_on_closure_of_ae_le ?_ hψc hu'c
    have hK' := (mem_obstacleSet_iff (d := 1) Ω).1 hu.1
    filter_upwards [hK', hψ, hu'] with x hx h1 h2
    rw [← h1, ← h2]
    exact hx
  -- `v_h = Π_h u ∈ K_h`
  obtain ⟨vh, hvhK, hfvh⟩ := exists_globalInterp_mem_discreteObstacleSet (𝒯 i) (hedge i) hψu hu'0
  -- `v = u^{h,*} = max (u_h, ψ) ∈ K`
  obtain ⟨w, hwK, hfw⟩ := exists_max_mem_obstacleSet hψ hψc (hψ2.mono_order (by norm_num)) hψ0
    hvc hv1 hv0
  -- Falk's lemma
  have hfalk := norm_sub_le_of_isVariationalInequalitySolution (L := 1) hc₀ hmono hlip huVI huhVI
    hwK hvhK
  simp only [sub_zero, add_zero, BilinForm.inner_toOperator, BilinForm.inner_rieszRep] at hfalk
  -- the two residuals
  have hres1 := residual_le_of_eq_load f g hΔ (w - uh i)
  have hres2 := residual_le_of_eq_load f g hΔ (vh - u)
  -- `‖u^{h,*} − u_h‖₀ ≤ ‖ψ − Π_h ψ‖₀ ≤ c h² |ψ|₂`
  have hL1 : (eLpNorm (SobolevMultiIndex.fn ((w - uh i : SobolevEuclideanZero 2 1 2 Ω)
      : SobolevEuclidean 2 1 2 Ω)) 2 (volume.restrict (Ω : Set 𝔼₂))).toReal
      ≤ c₀' * (𝒯 i).meshSize ^ 2 * Sψ := by
    have hae : SobolevMultiIndex.fn ((w - uh i : SobolevEuclideanZero 2 1 2 Ω)
        : SobolevEuclidean 2 1 2 Ω) =ᵐ[volume.restrict (Ω : Set 𝔼₂)]
        fun x ↦ max (v x) (ψ' x) - v x := by
      filter_upwards [SobolevMultiIndex.fn_sub (w : SobolevEuclidean 2 1 2 Ω) (uh i), hfw, hvh]
        with x h1 h2 h3
      have h1' : SobolevMultiIndex.fn ((w - uh i : SobolevEuclideanZero 2 1 2 Ω)
          : SobolevEuclidean 2 1 2 Ω) x
          = (SobolevMultiIndex.fn (w : SobolevEuclidean 2 1 2 Ω)
            - SobolevMultiIndex.fn (uh i : SobolevEuclidean 2 1 2 Ω)) x := h1
      rw [h1', Pi.sub_apply, h2, h3]
    have hest := hest₀ i ψ' hψ2 hψc
    simp only [Nat.sub_zero] at hest
    rw [eLpNorm_congr_ae hae, hSψ]
    exact toReal_le_of_le_ofReal_mul (by positivity) hSψfin
      ((eLpNorm_max_sub_le (𝒯 i) hψc hvc hvp hψv).trans
        ((eLpNorm_le_sobolevNorm_zero (memSobolev_sub_globalInterp_linear (𝒯 i) hψ2)).trans hest))
  -- `‖Π_h u − u‖₀ ≤ c h² |u|₂`
  have hL2 : (eLpNorm (SobolevMultiIndex.fn ((vh - u : SobolevEuclideanZero 2 1 2 Ω)
      : SobolevEuclidean 2 1 2 Ω)) 2 (volume.restrict (Ω : Set 𝔼₂))).toReal
      ≤ c₀' * (𝒯 i).meshSize ^ 2 * Su := by
    have hae : SobolevMultiIndex.fn ((vh - u : SobolevEuclideanZero 2 1 2 Ω)
        : SobolevEuclidean 2 1 2 Ω) =ᵐ[volume.restrict (Ω : Set 𝔼₂)]
        (𝒯 i).globalInterp referenceTriangleVertex baryCoord u' - u' := by
      filter_upwards [SobolevMultiIndex.fn_sub (vh : SobolevEuclidean 2 1 2 Ω) u, hfvh, hu']
        with x h1 h2 h3
      have h1' : SobolevMultiIndex.fn ((vh - u : SobolevEuclideanZero 2 1 2 Ω)
          : SobolevEuclidean 2 1 2 Ω) x
          = (SobolevMultiIndex.fn (vh : SobolevEuclidean 2 1 2 Ω)
            - SobolevMultiIndex.fn (u : SobolevEuclidean 2 1 2 Ω)) x := h1
      rw [h1', Pi.sub_apply, h2, h3, Pi.sub_apply]
    have hest := hest₀ i u' hu'2 hu'c
    simp only [Nat.sub_zero] at hest
    rw [eLpNorm_congr_ae hae, eLpNorm_sub_comm, hSu]
    exact toReal_le_of_le_ofReal_mul (by positivity) hSufin
      ((eLpNorm_le_sobolevNorm_zero (memSobolev_sub_globalInterp_linear (𝒯 i) hu'2)).trans hest)
  -- `‖u − Π_h u‖₁ ≤ C c h |u|₂`
  have hH1 : ‖u - vh‖ ≤ C * (c₁ * (𝒯 i).meshSize * Su) := by
    have h1 := Chapter10.norm_sub_le_of_fn_ae_eq hC u vh hu' hfvh
    have hest := hest₁ i u' hu'2 hu'c
    simp only [Nat.add_one_sub_one, pow_one] at hest
    rw [hSu]
    exact h1.trans (mul_le_mul_of_nonneg_left
      (toReal_le_of_le_ofReal_mul (by positivity) hSufin hest) hC0)
  -- assemble: `(c₀/2) ‖u − u_h‖² ≤ K h²`
  have hG0 : 0 ≤ ‖g - f‖ := norm_nonneg _
  have hR1 := hres1.trans (mul_le_mul_of_nonneg_left hL1 hG0)
  have hR2 := hres2.trans (mul_le_mul_of_nonneg_left hL2 hG0)
  have hH1' : ‖u - vh‖ ^ 2 ≤ (C * (c₁ * (𝒯 i).meshSize * Su)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hH1 2
  have hmain : (1 + (2 * R) ^ 2)⁻¹ / 2 * ‖u - uh i‖ ^ 2 ≤ K * (𝒯 i).meshSize ^ 2 := by
    rw [hK]
    refine hfalk.trans ?_
    calc _ ≤ ‖g - f‖ * (c₀' * (𝒯 i).meshSize ^ 2 * Sψ) + ‖g - f‖ * (c₀' * (𝒯 i).meshSize ^ 2 * Su)
          + 1 ^ 2 / (2 * (1 + (2 * R) ^ 2)⁻¹) * (C * (c₁ * (𝒯 i).meshSize * Su)) ^ 2 :=
          add_le_add (add_le_add hR1 hR2) (mul_le_mul_of_nonneg_left hH1' (by positivity))
      _ = _ := by ring
  have key : ∀ e : ℝ, e = 2 / (1 + (2 * R) ^ 2)⁻¹ * ((1 + (2 * R) ^ 2)⁻¹ / 2 * e) := fun e ↦ by
    have hne : (1 + (2 * R) ^ 2 : ℝ) ≠ 0 := by positivity
    field_simp
  have hsq : ‖u - uh i‖ ^ 2 ≤ 2 / (1 + (2 * R) ^ 2)⁻¹ * K * (𝒯 i).meshSize ^ 2 :=
    calc ‖u - uh i‖ ^ 2
        = 2 / (1 + (2 * R) ^ 2)⁻¹ * ((1 + (2 * R) ^ 2)⁻¹ / 2 * ‖u - uh i‖ ^ 2) := key _
      _ ≤ 2 / (1 + (2 * R) ^ 2)⁻¹ * (K * (𝒯 i).meshSize ^ 2) :=
          mul_le_mul_of_nonneg_left hmain (by positivity)
      _ = _ := by ring
  calc ‖u - uh i‖ = Real.sqrt (‖u - uh i‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (2 / (1 + (2 * R) ^ 2)⁻¹ * K * (𝒯 i).meshSize ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (2 / (1 + (2 * R) ^ 2)⁻¹ * K) * (𝒯 i).meshSize := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hh0]


end Example1143

/-! ### Theorem 11.4.5: the Lagrange multiplier of the simplified friction problem -/

section LagrangeMultiplier

open MeasureTheory TopologicalSpace
open scoped ContDiff ENNReal

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))} (B : BoundaryData Ω) (𝒯 : B.TraceFamily)

/-- `ℝ^N`, locally. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

/-- An element of `L^∞(μ)` of norm at most `g` is bounded by `g` almost everywhere. Helper;
Mathlib-facing (`MeasureTheory.Lp`). -/
theorem ae_abs_le_of_norm_le {μ : Measure 𝔼} {k : Lp ℝ ⊤ μ} {g : ℝ} (hk : ‖k‖ ≤ g) :
    ∀ᵐ x ∂μ, |k x| ≤ g := by
  have h1 : eLpNormEssSup k μ ≠ ⊤ := by
    have := Lp.eLpNorm_ne_top k
    rwa [eLpNorm_exponent_top (Lp.aestronglyMeasurable k)] at this
  have h2 : (eLpNormEssSup k μ).toReal ≤ g := by
    rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable k)] at hk
    exact hk
  filter_upwards [ae_le_eLpNormEssSup (f := k) (μ := μ)] with x hx
  rw [← Real.norm_eq_abs]
  refine le_trans ?_ h2
  rw [← ofReal_norm] at hx
  exact (ENNReal.ofReal_le_iff_le_toReal h1).1 hx

/-- **The Lagrange multiplier by Hahn–Banach and `(L¹)' = L^∞`**: a bounded functional `L` on
`H¹(Ω)` with `|L(w)| ≤ g ∫_Γ |γ w| dσ` — so that `L(w)` depends on the trace `γ w` only, as a
functional bounded in the `L¹(σ)` norm on the subspace `γ(H¹(Ω)) ⊆ L¹(σ)` — extends by the
Hahn–Banach theorem (`exists_extension_norm_eq`) to a functional on `L¹(σ)` of norm at most `g`,
which the Riesz representation `(L¹(σ))' = L^∞(σ)` (`MeasureTheory.Lp.toDual_surjective`,
`Numlib/MeasureTheory/Function/LpSpace/Duality.lean`) makes `h ↦ ∫ λ̄ h dσ` for some
`λ̄ ∈ L^∞(σ)` with `‖λ̄‖_∞ ≤ g`. The book's route through `H^{1/2}(Γ)` is not needed: the
subspace of `L¹(σ)` is the range of the trace, and the functional is transported to it through
the quotient `H¹(Ω)/ker` (`LinearMap.quotKerEquivRange`). -/
theorem exists_multiplier_of_forall_abs_le {g : ℝ} (hg : 0 ≤ g)
    (F : SobolevEuclidean N 1 2 Ω →L[ℝ] ℝ)
    (hF : ∀ w, |F w| ≤ g * ∫ x, |(𝒯.traceL 2 ENNReal.ofNat_ne_top w : 𝔼 → ℝ) x| ∂B.σ) :
    ∃ l : Lp ℝ ⊤ B.σ, ‖l‖ ≤ g ∧
      ∀ w, F w = ∫ x, l x * (𝒯.traceL 2 ENNReal.ofNat_ne_top w : 𝔼 → ℝ) x ∂B.σ := by
  -- the trace into `L¹(σ)`
  let ι : Lp ℝ 2 B.σ →ₗ[ℝ] Lp ℝ 1 B.σ :=
    { toFun := fun k ↦ ⟨(k : 𝔼 →ₘ[B.σ] ℝ), Lp.antitone one_le_two k.2⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let T : SobolevEuclidean N 1 2 Ω →ₗ[ℝ] Lp ℝ 1 B.σ :=
    ι ∘ₗ (𝒯.traceL 2 ENNReal.ofNat_ne_top).toLinearMap
  have hT : ∀ w, (T w : 𝔼 → ℝ) = (𝒯.traceL 2 ENNReal.ofNat_ne_top w : 𝔼 → ℝ) := fun w ↦ rfl
  have hTnorm : ∀ w, ‖T w‖ = ∫ x, |(𝒯.traceL 2 ENNReal.ofNat_ne_top w : 𝔼 → ℝ) x| ∂B.σ := by
    intro w
    rw [L1.norm_eq_integral_norm, hT]
    simp only [Real.norm_eq_abs]
  -- `F` vanishes on the kernel of `T`
  have hker : LinearMap.ker T ≤ LinearMap.ker (F : SobolevEuclidean N 1 2 Ω →ₗ[ℝ] ℝ) := by
    intro w hw
    rw [LinearMap.mem_ker] at hw ⊢
    have h := hF w
    rw [← hTnorm, hw, norm_zero, mul_zero] at h
    exact abs_nonpos_iff.1 h
  -- the functional on the range of `T`
  let Fq := (LinearMap.ker T).liftQ (F : SobolevEuclidean N 1 2 Ω →ₗ[ℝ] ℝ) hker
  let F' : LinearMap.range T →ₗ[ℝ] ℝ := Fq ∘ₗ T.quotKerEquivRange.symm.toLinearMap
  have hF' : ∀ w, F' ⟨T w, LinearMap.mem_range_self T w⟩ = F w := fun w ↦ by
    simp only [F', LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Fq]
    rfl
  have hbound : ∀ s : LinearMap.range T, ‖F' s‖ ≤ g * ‖s‖ := by
    rintro ⟨_, w, rfl⟩
    rw [hF' w, Real.norm_eq_abs]
    change |F w| ≤ g * ‖T w‖
    rw [hTnorm]
    exact hF w
  let F'' : LinearMap.range T →L[ℝ] ℝ := F'.mkContinuous g hbound
  have hF''norm : ‖F''‖ ≤ g := LinearMap.mkContinuous_norm_le _ hg _
  -- Hahn–Banach
  obtain ⟨G, hGext, hGnorm⟩ := exists_extension_norm_eq (LinearMap.range T) F''
  -- Riesz: `G = ∫ l ·` with `l ∈ L^∞`
  obtain ⟨l, hl⟩ := Lp.toDual_surjective (𝕜 := ℝ) (p := 1) (q := ⊤) (μ := B.σ)
    ENNReal.one_ne_top G
  refine ⟨l, ?_, fun w ↦ ?_⟩
  · rw [← (Lp.toDual ℝ 1 ⊤ B.σ).norm_map l, hl, hGnorm]
    exact hF''norm
  · have h1 := hGext ⟨T w, LinearMap.mem_range_self T w⟩
    rw [← hl, Lp.toDual_apply] at h1
    have h2 : F'' ⟨T w, LinearMap.mem_range_self T w⟩ = F w := by
      rw [LinearMap.mkContinuous_apply, hF']
    exact h2.symm.trans h1.symm

/-- `j(−w) = j(w)`. -/
theorem frictionFunctional_neg (g : ℝ) (w : SobolevEuclidean N 1 2 Ω) :
    frictionFunctional B 𝒯 g (-w) = frictionFunctional B 𝒯 g w := by
  simp only [frictionFunctional, map_neg]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_neg (𝒯.traceL 2 ENNReal.ofNat_ne_top w)] with x hx
  rw [hx, Pi.neg_apply, abs_neg]

/-- **(11.4.23) and the inequality of Exercise 11.3.10 for the friction problem**: a solution
`u` of (11.4.10) satisfies `a(u, u) + j(u) = ℓ(u)` (test with `v = 0` and `v = 2u`) and
`a(u, w) + j(w) ≥ ℓ(w)` for all `w` (test with `v = u + w`, `j` being subadditive). -/
theorem friction_eq_and_le_of_forall {g : ℝ} (hg : 0 ≤ g)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) {u : SobolevEuclidean N 1 2 Ω}
    (hu : ∀ v, Elliptic.load Ω f (v - u) ≤ Elliptic.laplaceForm Ω u (v - u)
      + frictionFunctional B 𝒯 g v - frictionFunctional B 𝒯 g u) :
    Elliptic.laplaceForm Ω u u + frictionFunctional B 𝒯 g u = Elliptic.load Ω f u ∧
      ∀ w, Elliptic.load Ω f w ≤ Elliptic.laplaceForm Ω u w + frictionFunctional B 𝒯 g w := by
  have h0 := hu 0
  have h2 := hu ((2 : ℝ) • u)
  have e0 : (0 : SobolevEuclidean N 1 2 Ω) - u = -u := zero_sub u
  have e2 : (2 : ℝ) • u - u = u := by rw [two_smul, add_sub_cancel_right]
  simp only [e0, frictionFunctional_zero] at h0
  simp only [e2, frictionFunctional_two_smul] at h2
  have h3 : Elliptic.load Ω f (-u) = -Elliptic.load Ω f u := map_neg _ _
  have h4 : Elliptic.laplaceForm Ω u (-u) = -Elliptic.laplaceForm Ω u u := map_neg _ _
  refine ⟨by linarith, fun w ↦ ?_⟩
  have h5 := hu (u + w)
  have e5 : u + w - u = w := add_sub_cancel_left u w
  simp only [e5] at h5
  have h6 := frictionFunctional_add_sub_le B 𝒯 hg u w
  rw [← frictionFunctional_apply] at h6
  linarith

/-- **Theorem 11.4.5 in the backbone's vocabulary**: `u ∈ H¹(Ω)` solves the friction problem
`a(u, v − u) + j(v) − j(u) ≥ ℓ(v − u)` for all `v` if and only if there is `λ ∈ L^∞(σ)` with
`|λ| ≤ 1` `σ`-a.e., `a(u, v) + g ∫_Γ λ γv dσ = ℓ(v)` for all `v` and `λ γu = |γu|` `σ`-a.e.
The book's proof: from the inequality, `a(u, u) + j(u) = ℓ(u)` and `|ℓ(v) − a(u, v)| ≤ j(v)`
(`friction_eq_and_le_of_forall`), so `ℓ − a(u, ·)` is represented on the traces by an
`L^∞(σ)` function of norm at most `g` (`exists_multiplier_of_forall_abs_le`), `λ` is its
quotient by `g`, and (11.4.22) follows from (11.4.21) at `v = u` and (11.4.23), the integrand
`|γu| − λ γu` being nonnegative with zero integral. Conversely (11.4.21) at `v − u`, with
`λ γv ≤ |γv|` and `λ γu = |γu|`, is the inequality. -/
theorem friction_multiplier_iff {g : ℝ} (hg : 0 < g) (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)))
    (u : SobolevEuclidean N 1 2 Ω) :
    (∀ v, Elliptic.laplaceForm Ω u (v - u) + frictionFunctional B 𝒯 g v
        - frictionFunctional B 𝒯 g u ≥ Elliptic.load Ω f (v - u)) ↔
      ∃ l : Lp ℝ ⊤ B.σ, (∀ᵐ x ∂B.σ, |l x| ≤ 1) ∧
        (∀ v, Elliptic.laplaceForm Ω u v
          + g * ∫ x, l x * (𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x ∂B.σ
          = Elliptic.load Ω f v) ∧
        ∀ᵐ x ∂B.σ, l x * (𝒯.traceL 2 ENNReal.ofNat_ne_top u : 𝔼 → ℝ) x
          = |(𝒯.traceL 2 ENNReal.ofNat_ne_top u : 𝔼 → ℝ) x| := by
  have hI : ∀ k : Lp ℝ 2 B.σ, Integrable (fun x ↦ |k x|) B.σ := fun k ↦
    ((Lp.memLp k).integrable one_le_two).abs
  have hIl : ∀ (l : Lp ℝ ⊤ B.σ) (k : Lp ℝ 2 B.σ), Integrable (fun x ↦ l x * k x) B.σ :=
    fun l k ↦ (Lp.memLp l).integrable_mul ((Lp.memLp k).mono_exponent one_le_two)
  constructor
  · intro hu
    replace hu : ∀ v, Elliptic.load Ω f (v - u) ≤ Elliptic.laplaceForm Ω u (v - u)
        + frictionFunctional B 𝒯 g v - frictionFunctional B 𝒯 g u := fun v ↦ hu v
    obtain ⟨h23, h24⟩ := friction_eq_and_le_of_forall B 𝒯 hg.le f hu
    -- the functional `L(w) = ℓ(w) − a(u, w)` is bounded by `j(w)`
    obtain ⟨F, hFdef⟩ : ∃ F : SobolevEuclidean N 1 2 Ω →L[ℝ] ℝ,
        F = Elliptic.load Ω f - Elliptic.laplaceForm Ω u := ⟨_, rfl⟩
    have hFapply : ∀ w, F w = Elliptic.load Ω f w - Elliptic.laplaceForm Ω u w := fun w ↦ by
      rw [hFdef]; rfl
    have hF : ∀ w, |F w| ≤ g * ∫ x, |(𝒯.traceL 2 ENNReal.ofNat_ne_top w : 𝔼 → ℝ) x| ∂B.σ := by
      intro w
      have h1 := h24 w
      have h2 := h24 (-w)
      have h3 : Elliptic.load Ω f (-w) = -Elliptic.load Ω f w := map_neg _ _
      have h4 : Elliptic.laplaceForm Ω u (-w) = -Elliptic.laplaceForm Ω u w := map_neg _ _
      rw [frictionFunctional_neg] at h2
      rw [← frictionFunctional_apply, hFapply, abs_le]
      constructor <;> linarith
    obtain ⟨l, hl, hFl⟩ := exists_multiplier_of_forall_abs_le B 𝒯 hg.le F hF
    have hlg := ae_abs_le_of_norm_le hl
    refine ⟨g⁻¹ • l, ?_, fun v ↦ ?_, ?_⟩
    · filter_upwards [hlg, Lp.coeFn_smul g⁻¹ l] with x hx hx'
      rw [hx', Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.2 hg)]
      calc g⁻¹ * |l x| ≤ g⁻¹ * g := by gcongr
        _ = 1 := inv_mul_cancel₀ hg.ne'
    · have e : ∫ x, (g⁻¹ • l : Lp ℝ ⊤ B.σ) x * (𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x
          ∂B.σ = g⁻¹ * ∫ x, l x * (𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x ∂B.σ := by
        rw [← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul g⁻¹ l] with x hx
        rw [hx, Pi.smul_apply, smul_eq_mul, mul_assoc]
      rw [e, ← mul_assoc, mul_inv_cancel₀ hg.ne', one_mul, ← hFl, hFapply]
      ring
    · -- (11.4.22)
      have h21 := hFl u
      rw [hFapply] at h21
      have hgu : ∫ x, l x * (𝒯.traceL 2 ENNReal.ofNat_ne_top u : 𝔼 → ℝ) x ∂B.σ
          = g * ∫ x, |(𝒯.traceL 2 ENNReal.ofNat_ne_top u : 𝔼 → ℝ) x| ∂B.σ := by
        rw [← frictionFunctional_apply]; linarith
      have hnn : 0 ≤ᵐ[B.σ] fun x ↦ g * |(𝒯.traceL 2 ENNReal.ofNat_ne_top u : 𝔼 → ℝ) x|
          - l x * (𝒯.traceL 2 ENNReal.ofNat_ne_top u : 𝔼 → ℝ) x := by
        filter_upwards [hlg] with x hx
        have : l x * (𝒯.traceL 2 ENNReal.ofNat_ne_top u : 𝔼 → ℝ) x
            ≤ g * |(𝒯.traceL 2 ENNReal.ofNat_ne_top u : 𝔼 → ℝ) x| := by
          calc l x * (𝒯.traceL 2 ENNReal.ofNat_ne_top u : 𝔼 → ℝ) x
              ≤ |l x * (𝒯.traceL 2 ENNReal.ofNat_ne_top u : 𝔼 → ℝ) x| := le_abs_self _
            _ = |l x| * |(𝒯.traceL 2 ENNReal.ofNat_ne_top u : 𝔼 → ℝ) x| := abs_mul _ _
            _ ≤ g * |(𝒯.traceL 2 ENNReal.ofNat_ne_top u : 𝔼 → ℝ) x| := by gcongr
        simp only [Pi.zero_apply]
        linarith
      have hzero : ∫ x, (g * |(𝒯.traceL 2 ENNReal.ofNat_ne_top u : 𝔼 → ℝ) x|
          - l x * (𝒯.traceL 2 ENNReal.ofNat_ne_top u : 𝔼 → ℝ) x) ∂B.σ = 0 := by
        rw [integral_sub ((hI _).const_mul g) (hIl l _), integral_const_mul, hgu, sub_self]
      have hae := (integral_eq_zero_iff_of_nonneg_ae hnn
        (((hI _).const_mul g).sub (hIl l _))).1 hzero
      filter_upwards [hae, Lp.coeFn_smul g⁻¹ l] with x hx hx'
      simp only [Pi.zero_apply] at hx
      rw [hx', Pi.smul_apply, smul_eq_mul, mul_assoc]
      have : l x * (𝒯.traceL 2 ENNReal.ofNat_ne_top u : 𝔼 → ℝ) x
          = g * |(𝒯.traceL 2 ENNReal.ofNat_ne_top u : 𝔼 → ℝ) x| := by linarith
      rw [this, ← mul_assoc, inv_mul_cancel₀ hg.ne', one_mul]
  · rintro ⟨l, hl1, h21, h22⟩ v
    have hv := h21 v
    have hu := h21 u
    have hjv : g * ∫ x, l x * (𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x ∂B.σ
        ≤ frictionFunctional B 𝒯 g v := by
      rw [frictionFunctional_apply]
      refine mul_le_mul_of_nonneg_left (integral_mono_ae (hIl l _) (hI _) ?_) hg.le
      filter_upwards [hl1] with x hx
      calc l x * (𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x
          ≤ |l x * (𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x| := le_abs_self _
        _ = |l x| * |(𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x| := abs_mul _ _
        _ ≤ 1 * |(𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x| := by gcongr
        _ = _ := one_mul _
    have hju : g * ∫ x, l x * (𝒯.traceL 2 ENNReal.ofNat_ne_top u : 𝔼 → ℝ) x ∂B.σ
        = frictionFunctional B 𝒯 g u := by
      rw [frictionFunctional_apply]
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [h22] with x hx
      rw [hx]
    have e1 : Elliptic.laplaceForm Ω u (v - u)
        = Elliptic.laplaceForm Ω u v - Elliptic.laplaceForm Ω u u := map_sub _ _ _
    have e2 : Elliptic.load Ω f (v - u) = Elliptic.load Ω f v - Elliptic.load Ω f u :=
      map_sub _ _ _
    rw [ge_iff_le, e1, e2]
    linarith

/-- **Theorem 11.4.5 (the Lagrange multiplier of the simplified friction problem)**, over the
boundary interface `B : BoundaryData Ω`, `𝒯 : B.TraceFamily` of
`Numlib/Analysis/Sobolev/Boundary/Data.lean` (a bounded `C¹` domain, `IsContDiffDomain.traceFamily`,
or a polygon without slits, `Triangulation.traceFamily` — the book's Lipschitz domain), with
`Λ = {μ ∈ L^∞(Γ) : |μ| ≤ 1 a.e. on Γ}`: for `g > 0` and `f ∈ L²(Ω)`, `u ∈ V = H¹(Ω)` solves the
simplified friction problem (11.4.10) = (11.1.13),

  `∫_Ω [∇u·∇(v − u) + u (v − u)] + g ∫_Γ (|v| − |u|) ds ≥ ∫_Ω f (v − u)`  for all `v ∈ V`,

if and only if there is `λ ∈ Λ` such that

  `∫_Ω (∇u·∇v + u v) dx + g ∫_Γ λ v ds = ∫_Ω f v dx`  for all `v ∈ V`  (11.4.21),
  `λ u = |u|`  a.e. on `Γ`  (11.4.22);

the multiplier is unique (`theorem_11_4_5_unique`). The proof is the book's, except that the
extension of `L(v) = ℓ(v) − a(u, v)` from the traces to `L¹(Γ)` by Hahn–Banach and the duality
`(L¹(Γ))' = L^∞(Γ)` need no fractional space `H^{1/2}(Γ)` (`friction_multiplier_iff`,
`exists_multiplier_of_forall_abs_le`). -/
theorem theorem_11_4_5 {g : ℝ} (hg : 0 < g) (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)))
    (u : SobolevEuclidean N 1 2 Ω) :
    (∀ v : SobolevEuclidean N 1 2 Ω,
      ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn (v - u) x
        ≤ (∫ x in (Ω : Set 𝔼), ((∑ i, SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
            * SobolevMultiIndex.weakDeriv (v - u) (MultiIndexLE.single i) x)
            + SobolevMultiIndex.fn u x * SobolevMultiIndex.fn (v - u) x))
          + g * ∫ x, (|(𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x|
            - |(𝒯.traceL 2 ENNReal.ofNat_ne_top u : 𝔼 → ℝ) x|) ∂B.σ) ↔
      ∃ l : Lp ℝ ⊤ B.σ, (∀ᵐ x ∂B.σ, |l x| ≤ 1) ∧
        (∀ v : SobolevEuclidean N 1 2 Ω,
          (∫ x in (Ω : Set 𝔼), ((∑ i, SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
              * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) x)
              + SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x))
            + g * ∫ x, l x * (𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x ∂B.σ
            = ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn v x) ∧
        ∀ᵐ x ∂B.σ, l x * (𝒯.traceL 2 ENNReal.ofNat_ne_top u : 𝔼 → ℝ) x
          = |(𝒯.traceL 2 ENNReal.ofNat_ne_top u : 𝔼 → ℝ) x| := by
  have h := friction_multiplier_iff B 𝒯 hg f u
  simp only [ge_iff_le, Elliptic.laplaceForm_apply, Elliptic.load_apply] at h
  refine (forall_congr' fun v ↦ (friction_ineq_iff B 𝒯 g f u v).trans ?_).trans h
  rw [Elliptic.laplaceForm_apply, Elliptic.load_apply]

/-- **Theorem 11.4.5, uniqueness of the Lagrange multiplier**: two elements of `L^∞(Γ)` both
satisfying (11.4.21) for the same `u` agree. Their difference `μ` satisfies
`∫_Γ μ γv ds = 0` for all `v ∈ H¹(Ω)`, in particular against the restrictions of all smooth
compactly supported functions (whose traces they are, `TraceFamily.traceL_ae_eq`), so `μ = 0`
`σ`-a.e. by `ae_eq_zero_of_integral_contDiff_smul_eq_zero` — no density of `H^{1/2}(Γ)` in
`L²(Γ)` is needed. -/
theorem theorem_11_4_5_unique {g : ℝ} (hg : 0 < g) (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)))
    (u : SobolevEuclidean N 1 2 Ω) {l l' : Lp ℝ ⊤ B.σ}
    (hl : ∀ v : SobolevEuclidean N 1 2 Ω,
      (∫ x in (Ω : Set 𝔼), ((∑ i, SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
          * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) x)
          + SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x))
        + g * ∫ x, l x * (𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x ∂B.σ
        = ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn v x)
    (hl' : ∀ v : SobolevEuclidean N 1 2 Ω,
      (∫ x in (Ω : Set 𝔼), ((∑ i, SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
          * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) x)
          + SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x))
        + g * ∫ x, l' x * (𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x ∂B.σ
        = ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn v x) :
    l = l' := by
  have hIl : ∀ (l : Lp ℝ ⊤ B.σ) (k : Lp ℝ 2 B.σ), Integrable (fun x ↦ l x * k x) B.σ :=
    fun l k ↦ (Lp.memLp l).integrable_mul ((Lp.memLp k).mono_exponent one_le_two)
  -- `∫ (l − l') γ v dσ = 0` for all `v`
  have hdiff : ∀ v : SobolevEuclidean N 1 2 Ω,
      ∫ x, (l - l' : Lp ℝ ⊤ B.σ) x * (𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x ∂B.σ = 0 := by
    intro v
    have h1 := hl v
    have h2 := hl' v
    have e : ∫ x, (l - l' : Lp ℝ ⊤ B.σ) x * (𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x ∂B.σ
        = (∫ x, l x * (𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x ∂B.σ)
          - ∫ x, l' x * (𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x ∂B.σ := by
      rw [← integral_sub (hIl l _) (hIl l' _)]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_sub l l'] with x hx
      rw [hx, Pi.sub_apply, sub_mul]
    rw [e]
    have : g * ((∫ x, l x * (𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x ∂B.σ)
        - ∫ x, l' x * (𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x ∂B.σ) = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hg.ne'
  -- hence against every smooth compactly supported function
  have hsm : ∀ ψ : 𝔼 → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∫ x, ψ x • (l - l' : Lp ℝ ⊤ B.σ) x ∂B.σ = 0 := by
    intro ψ hψ hψc
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
    obtain ⟨W, hW⟩ : ∃ W : SobolevEuclidean N 1 2 Ω,
        SobolevMultiIndex.fn W =ᵐ[volume.restrict (Ω : Set 𝔼)] ψ :=
      hψ1.exists_sobolevMultiIndex_of_hasCompactSupport' hψc
    have hγW := 𝒯.traceL_ae_eq 2 ENNReal.ofNat_ne_top W ψ hW hψ.continuous.continuousOn
    rw [← hdiff W]
    refine integral_congr_ae ?_
    filter_upwards [hγW] with x hx
    rw [hx, smul_eq_mul, mul_comm]
  have hloc : LocallyIntegrable (l - l' : Lp ℝ ⊤ B.σ) B.σ :=
    ((Lp.memLp (l - l')).integrable le_top).locallyIntegrable
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc hsm
  rw [← sub_eq_zero]
  refine Lp.eq_zero_iff_ae_eq_zero.2 ?_
  filter_upwards [hae] with x hx
  exact hx

end LagrangeMultiplier

/-! ### Example 11.4.4: the friction problem with linear elements on a polygon

The error estimate `‖u − u_h‖_{H¹(Ω)} ≤ c(u) h` for the linear finite element solution of the
simplified friction problem (11.1.13) = (11.4.10) on a polygon.  The section is in three parts:
the residual of the continuous solution, read by Green's formula (any `BoundaryData`), the
`L²(Γ)` error of the linear interpolant on a triangulated polygon (the edge bookkeeping), and the
assembly through Falk's lemma. -/

section Residual

open MeasureTheory TopologicalSpace SobolevMultiIndex

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))} {B : BoundaryData Ω} (𝒯 : B.TraceFamily)

/-- `ℝ^N`, locally. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

/-- The standard basis of `ℝ^N`, locally. -/
local notation "𝔅" => OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin N) ℝ)

/-- `‖k‖² = ∫ k²` in `L²(μ)`. Helper; Mathlib-facing (`MeasureTheory.L2Space`). -/
theorem norm_sq_eq_integral_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} (k : Lp ℝ 2 μ) :
    ‖k‖ ^ 2 = ∫ x, k x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_eq_integral_mul]
  exact integral_congr_ae (Eventually.of_forall fun x ↦ (sq _).symm)

/-- **The weak Laplacian of an `H²(Ω)` function**, `Δ_w u = ∑ᵢ ∂ᵢ(∂ᵢu) ∈ L²(Ω)`. -/
noncomputable def weakLaplacian (U : SobolevEuclidean N 2 2 Ω) :
    Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)) :=
  ∑ i, weakDeriv (partialDerivL ℝ 𝔅 2 Ω volume i U) (MultiIndexLE.single i)

/-- **The datum of the residual of Example 11.4.4**, `−Δu + u − f ∈ L²(Ω)`. -/
noncomputable def frictionResidualData (U : SobolevEuclidean N 2 2 Ω)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)) :=
  -weakLaplacian U + weakDeriv U 0 - f

/-- **Green's formula as the residual identity** (the display of Example 11.4.4): for `u ∈ H²(Ω)`
read in `H¹(Ω)` and every `w ∈ H¹(Ω)`,

  `a(u, w) − ℓ(w) = ∫_Γ (∂u/∂ν) (γ w) ds + ∫_Ω (−Δu + u − f) w dx`,

the boundary term being the normal trace `BoundaryData.TraceFamily.normalTrace` of
`Numlib/Analysis/Sobolev/Boundary/Data.lean` (Green's formula for `u ∈ H²`, `w ∈ H¹`). -/
theorem laplaceForm_sub_load_eq_normalTrace_add (U : SobolevEuclidean N 2 2 Ω)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) (w : SobolevEuclidean N 1 2 Ω) :
    Elliptic.laplaceForm Ω (toLowerOrderL ℝ 𝔅 2 Ω volume (by norm_num : (1 : ℕ) ≤ 2) U) w
        - Elliptic.load Ω f w
      = (∫ x, 𝒯.normalTrace U x * (𝒯.traceL 2 ENNReal.ofNat_ne_top w : 𝔼 → ℝ) x ∂B.σ)
        + Elliptic.load Ω (frictionResidualData U f) w := by
  have hgreen := 𝒯.green_laplacian U w
  have hI1 : Integrable (fun x ↦ ∑ i, (weakDeriv U (MultiIndexLE.singleLE i) : 𝔼 → ℝ) x
      * (weakDeriv w (MultiIndexLE.single i) : 𝔼 → ℝ) x)
      (volume.restrict (Ω : Set 𝔼)) :=
    integrable_finsetSum _ fun i _ ↦ (Lp.memLp _).integrable_mul (Lp.memLp _)
  have hI2 : Integrable (fun x ↦ fn U x * fn w x) (volume.restrict (Ω : Set 𝔼)) :=
    (Lp.memLp (weakDeriv U 0)).integrable_mul (Lp.memLp (weakDeriv w 0))
  have hI3 : Integrable (fun x ↦ f x * fn w x) (volume.restrict (Ω : Set 𝔼)) :=
    (Lp.memLp f).integrable_mul (Lp.memLp (weakDeriv w 0))
  have hI4 : Integrable (fun x ↦ (weakLaplacian U : 𝔼 → ℝ) x * fn w x)
      (volume.restrict (Ω : Set 𝔼)) :=
    (Lp.memLp _).integrable_mul (Lp.memLp (weakDeriv w 0))
  -- the weak Laplacian, as a function
  have hD : (weakLaplacian U : 𝔼 → ℝ) =ᵐ[volume.restrict (Ω : Set 𝔼)]
      fun x ↦ ∑ i, (weakDeriv (partialDerivL ℝ 𝔅 2 Ω volume i U) (MultiIndexLE.single i) :
        𝔼 → ℝ) x := by
    have h := Lp.coeFn_finsetSum Finset.univ
      (fun i ↦ weakDeriv (partialDerivL ℝ 𝔅 2 Ω volume i U) (MultiIndexLE.single i))
    rw [weakLaplacian]
    filter_upwards [h] with x hx
    rw [hx, Finset.sum_apply]
  have hgreen' : (∫ x in (Ω : Set 𝔼), (weakLaplacian U : 𝔼 → ℝ) x * fn w x)
      + ∫ x in (Ω : Set 𝔼), ∑ i, (weakDeriv U (MultiIndexLE.singleLE i) : 𝔼 → ℝ) x
          * (weakDeriv w (MultiIndexLE.single i) : 𝔼 → ℝ) x
      = ∫ x, 𝒯.normalTrace U x * (𝒯.traceL 2 ENNReal.ofNat_ne_top w : 𝔼 → ℝ) x ∂B.σ := by
    have e : ∫ x in (Ω : Set 𝔼), (weakLaplacian U : 𝔼 → ℝ) x * fn w x
        = ∫ x in (Ω : Set 𝔼), (∑ i, (weakDeriv (partialDerivL ℝ 𝔅 2 Ω volume i U)
            (MultiIndexLE.single i) : 𝔼 → ℝ) x) * fn w x :=
      integral_congr_ae (hD.mono fun x hx ↦ by dsimp only; rw [hx])
    rw [e, hgreen]
  -- the left-hand side
  have hlhs : Elliptic.laplaceForm Ω (toLowerOrderL ℝ 𝔅 2 Ω volume (by norm_num : (1 : ℕ) ≤ 2) U) w
      = (∫ x in (Ω : Set 𝔼), ∑ i, (weakDeriv U (MultiIndexLE.singleLE i) : 𝔼 → ℝ) x
          * (weakDeriv w (MultiIndexLE.single i) : 𝔼 → ℝ) x)
        + ∫ x in (Ω : Set 𝔼), fn U x * fn w x := by
    rw [Elliptic.laplaceForm_apply, ← integral_add hI1 hI2]
    rfl
  -- the residual datum, as a function
  have hR : (frictionResidualData U f : 𝔼 → ℝ) =ᵐ[volume.restrict (Ω : Set 𝔼)]
      fun x ↦ -(weakLaplacian U : 𝔼 → ℝ) x + fn U x - f x := by
    filter_upwards [Lp.coeFn_sub (-weakLaplacian U + weakDeriv U 0) f,
      Lp.coeFn_add (-weakLaplacian U) (weakDeriv U 0), Lp.coeFn_neg (weakLaplacian U)]
      with x h1 h2 h3
    simp only [frictionResidualData, h1, Pi.sub_apply, h2, Pi.add_apply, h3, Pi.neg_apply]
    rfl
  have hrhs : Elliptic.load Ω (frictionResidualData U f) w
      = -(∫ x in (Ω : Set 𝔼), (weakLaplacian U : 𝔼 → ℝ) x * fn w x)
        + (∫ x in (Ω : Set 𝔼), fn U x * fn w x) - ∫ x in (Ω : Set 𝔼), f x * fn w x := by
    have e : ∫ x in (Ω : Set 𝔼), (frictionResidualData U f : 𝔼 → ℝ) x * fn w x
        = ∫ x in (Ω : Set 𝔼), (-(weakLaplacian U : 𝔼 → ℝ) x + fn U x - f x) * fn w x :=
      integral_congr_ae (hR.mono fun x hx ↦ by dsimp only; rw [hx])
    have hI4' : Integrable (fun x ↦ -((weakLaplacian U : 𝔼 → ℝ) x * fn w x))
        (volume.restrict (Ω : Set 𝔼)) := hI4.neg
    have hI5 : Integrable (fun x ↦ -((weakLaplacian U : 𝔼 → ℝ) x * fn w x) + fn U x * fn w x)
        (volume.restrict (Ω : Set 𝔼)) := hI4'.add hI2
    have e2 : ∫ x in (Ω : Set 𝔼), (-(weakLaplacian U : 𝔼 → ℝ) x + fn U x - f x) * fn w x
        = (∫ x in (Ω : Set 𝔼), (-((weakLaplacian U : 𝔼 → ℝ) x * fn w x) + fn U x * fn w x))
          - ∫ x in (Ω : Set 𝔼), f x * fn w x := by
      rw [← integral_sub hI5 hI3]
      exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
    have e3 : (∫ x in (Ω : Set 𝔼), (-((weakLaplacian U : 𝔼 → ℝ) x * fn w x) + fn U x * fn w x))
        = -(∫ x in (Ω : Set 𝔼), (weakLaplacian U : 𝔼 → ℝ) x * fn w x)
          + ∫ x in (Ω : Set 𝔼), fn U x * fn w x := by
      rw [integral_add hI4' hI2, integral_neg]
    rw [Elliptic.load_apply, e, e2, e3]
  rw [hlhs, hrhs, Elliptic.load_apply, ← hgreen']
  ring

/-- **The normal derivative of an `H²(Ω)` function as an element of `L²(Γ)`**, so that
`‖∂u/∂ν‖_{L²(Γ)}` is a norm. -/
noncomputable def normalTraceL (U : SobolevEuclidean N 2 2 Ω) : Lp ℝ 2 B.σ :=
  (𝒯.memLp_normalTrace U).toLp _

/-- **The bound on the residual of Example 11.4.4**: for the solution `u ∈ H²(Ω)` of the friction
problem and any `v ∈ H¹(Ω)`,

  `|R(v, u)| ≤ (‖∂u/∂ν‖_{L²(Γ)} + g √(meas Γ)) ‖γ(v − u)‖_{L²(Γ)}
      + ‖−Δu + u − f‖_{L²(Ω)} ‖v − u‖_{L²(Ω)}`,

`R(v, u) = a(u, v − u) + j(v) − j(u) − ℓ(v − u)` being the residual of Falk's lemma: the
integration by parts `laplaceForm_sub_load_eq_normalTrace_add`, Cauchy–Schwarz on `Γ` and on `Ω`,
and `||γv| − |γu|| ≤ |γ(v − u)|` for the friction term. -/
theorem abs_residual_le {g : ℝ} (hg : 0 ≤ g) {U : SobolevEuclidean N 2 2 Ω}
    {u : SobolevEuclidean N 1 2 Ω}
    (hU : toLowerOrderL ℝ 𝔅 2 Ω volume (by norm_num : (1 : ℕ) ≤ 2) U = u)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) (v : SobolevEuclidean N 1 2 Ω) :
    |Elliptic.laplaceForm Ω u (v - u) + frictionFunctional B 𝒯 g v
        - frictionFunctional B 𝒯 g u - Elliptic.load Ω f (v - u)|
      ≤ (‖normalTraceL 𝒯 U‖ + g * (eLpNorm (fun _ : 𝔼 ↦ (1 : ℝ)) 2 B.σ).toReal)
          * ‖𝒯.traceL 2 ENNReal.ofNat_ne_top (v - u)‖
        + ‖frictionResidualData U f‖ * ‖weakDeriv (v - u) 0‖ := by
  have hI : ∀ k : Lp ℝ 2 B.σ, Integrable (fun x ↦ |k x|) B.σ := fun k ↦
    ((Lp.memLp k).integrable one_le_two).abs
  have hgreen := laplaceForm_sub_load_eq_normalTrace_add 𝒯 U f (v - u)
  rw [hU] at hgreen
  -- the boundary term
  have hnt : (∫ x, 𝒯.normalTrace U x * (𝒯.traceL 2 ENNReal.ofNat_ne_top (v - u) : 𝔼 → ℝ) x ∂B.σ)
      = ⟪normalTraceL 𝒯 U, 𝒯.traceL 2 ENNReal.ofNat_ne_top (v - u)⟫_ℝ := by
    rw [L2.inner_eq_integral_mul]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (𝒯.memLp_normalTrace U)] with x hx
    rw [normalTraceL, hx]
  have hnt' : |∫ x, 𝒯.normalTrace U x
      * (𝒯.traceL 2 ENNReal.ofNat_ne_top (v - u) : 𝔼 → ℝ) x ∂B.σ|
      ≤ ‖normalTraceL 𝒯 U‖ * ‖𝒯.traceL 2 ENNReal.ofNat_ne_top (v - u)‖ := by
    rw [hnt]
    exact abs_real_inner_le_norm _ _
  -- the friction term
  have hjdiff : |frictionFunctional B 𝒯 g v - frictionFunctional B 𝒯 g u|
      ≤ g * (eLpNorm (fun _ : 𝔼 ↦ (1 : ℝ)) 2 B.σ).toReal
        * ‖𝒯.traceL 2 ENNReal.ofNat_ne_top (v - u)‖ := by
    have hsub : (𝒯.traceL 2 ENNReal.ofNat_ne_top (v - u) : 𝔼 → ℝ)
        =ᵐ[B.σ] fun x ↦ (𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x
          - (𝒯.traceL 2 ENNReal.ofNat_ne_top u : 𝔼 → ℝ) x := by
      rw [map_sub]
      filter_upwards [Lp.coeFn_sub (𝒯.traceL 2 ENNReal.ofNat_ne_top v)
        (𝒯.traceL 2 ENNReal.ofNat_ne_top u)] with x hx
      rw [hx, Pi.sub_apply]
    have hle : |(∫ x, |(𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x| ∂B.σ)
        - ∫ x, |(𝒯.traceL 2 ENNReal.ofNat_ne_top u : 𝔼 → ℝ) x| ∂B.σ|
        ≤ ∫ x, |(𝒯.traceL 2 ENNReal.ofNat_ne_top (v - u) : 𝔼 → ℝ) x| ∂B.σ := by
      rw [← integral_sub (hI _) (hI _)]
      refine (abs_integral_le_integral_abs).trans (integral_mono_ae (((hI _).sub (hI _)).abs)
        (hI _) ?_)
      filter_upwards [hsub] with x hx
      rw [hx]
      exact abs_abs_sub_abs_le_abs_sub _ _
    have hfin := integral_abs_le_mul_norm B (𝒯.traceL 2 ENNReal.ofNat_ne_top (v - u))
    rw [frictionFunctional_apply, frictionFunctional_apply, ← mul_sub, abs_mul, abs_of_nonneg hg,
      mul_assoc]
    exact mul_le_mul_of_nonneg_left (hle.trans hfin) hg
  -- the interior term
  have hload : |Elliptic.load Ω (frictionResidualData U f) (v - u)|
      ≤ ‖frictionResidualData U f‖ * ‖weakDeriv (v - u) 0‖ :=
    Elliptic.abs_load_le Ω _ _
  have hsplit : Elliptic.laplaceForm Ω u (v - u) + frictionFunctional B 𝒯 g v
      - frictionFunctional B 𝒯 g u - Elliptic.load Ω f (v - u)
      = ((∫ x, 𝒯.normalTrace U x * (𝒯.traceL 2 ENNReal.ofNat_ne_top (v - u) : 𝔼 → ℝ) x ∂B.σ)
          + Elliptic.load Ω (frictionResidualData U f) (v - u))
        + (frictionFunctional B 𝒯 g v - frictionFunctional B 𝒯 g u) := by
    rw [← hgreen]; ring
  rw [hsplit]
  calc |((∫ x, 𝒯.normalTrace U x
        * (𝒯.traceL 2 ENNReal.ofNat_ne_top (v - u) : 𝔼 → ℝ) x ∂B.σ)
          + Elliptic.load Ω (frictionResidualData U f) (v - u))
        + (frictionFunctional B 𝒯 g v - frictionFunctional B 𝒯 g u)|
      ≤ (|∫ x, 𝒯.normalTrace U x * (𝒯.traceL 2 ENNReal.ofNat_ne_top (v - u) : 𝔼 → ℝ) x ∂B.σ|
          + |Elliptic.load Ω (frictionResidualData U f) (v - u)|)
        + |frictionFunctional B 𝒯 g v - frictionFunctional B 𝒯 g u| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (‖normalTraceL 𝒯 U‖ * ‖𝒯.traceL 2 ENNReal.ofNat_ne_top (v - u)‖
          + ‖frictionResidualData U f‖ * ‖weakDeriv (v - u) 0‖)
        + g * (eLpNorm (fun _ : 𝔼 ↦ (1 : ℝ)) 2 B.σ).toReal
          * ‖𝒯.traceL 2 ENNReal.ofNat_ne_top (v - u)‖ :=
        add_le_add (add_le_add hnt' hload) hjdiff
    _ = _ := by ring

end Residual

/-! #### The `L²(Γ)` error of the linear interpolant on a polygon

The boundary edges of a triangulation of a polygon lie on the finitely many sides of the polygon;
along a side the linear interpolant is the one-dimensional affine interpolant of the restriction
of `u` at the ends of the edge, so the panel estimate
`integral_sq_sub_piecewiseLinearInterpCLM_le` of `Numlib/Approximation/SobolevInterpolation.lean`
applies on each edge and the edges of one side have disjoint parameter intervals. -/

section EdgeInterpolation

open MeasureTheory TopologicalSpace EuclideanSpace SobolevMultiIndex intervalIntegral

/-- `ℝ²`, locally. -/
local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

/-- A finite sum of integrals of a nonnegative function over pairwise disjoint measurable subsets
of `J` is at most the integral over `J`. -/
theorem sum_setIntegral_le_of_pairwiseDisjoint {ι : Type*} (S : Finset ι) {I : ι → Set ℝ}
    {J : Set ℝ} {F : ℝ → ℝ} (hI : ∀ e ∈ S, MeasurableSet (I e)) (hIJ : ∀ e ∈ S, I e ⊆ J)
    (hdisj : (S : Set ι).PairwiseDisjoint I) (hF : IntegrableOn F J) (hF0 : ∀ x, 0 ≤ F x) :
    ∑ e ∈ S, ∫ x in I e, F x ≤ ∫ x in J, F x := by
  rw [← integral_biUnion_finset S hI hdisj fun e he ↦ hF.mono_set (hIJ e he)]
  exact setIntegral_mono_set hF (Eventually.of_forall hF0)
    (LE.le.eventuallySubset (iUnion₂_subset hIJ))

/-- **The one-panel affine interpolation estimate** on a sub-interval `[s, t] ⊆ [0, 1]` for the
`C¹` representative `f` of an element `U ∈ H²(0, 1)`: `∫_s^t (f − G)² ≤ (t − s)⁴ ∫_s^t |U''|²`
when `G` is the affine interpolant of `f` at `s` and `t`
(`integral_sq_sub_piecewiseLinearInterpCLM_le` with the one-panel partition `{s, t}`). -/
theorem integral_sq_sub_affine_le (U : SobolevInterval 2 0 1) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hfU : ∀ r ∈ Icc (0 : ℝ) 1, ∀ r' ∈ Icc (0 : ℝ) 1,
      deriv f r' - deriv f r = ∫ x in r..r', SobolevInterval.deriv U (Fin.last 2) x)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1) {G : ℝ → ℝ}
    (hG : ∀ r ∈ Icc s t, G r = f s + (f t - f s) * ((r - s) / (t - s))) :
    ∫ r in s..t, (f r - G r) ^ 2
      ≤ (t - s) ^ 4 * ∫ r in s..t, SobolevInterval.deriv U (Fin.last 2) r ^ 2 := by
  let x : ℕ → Icc s t := fun j ↦
    if j = 0 then ⟨s, left_mem_Icc.2 hst.le⟩ else ⟨t, right_mem_Icc.2 hst.le⟩
  have hx0 : (x 0 : ℝ) = s := by simp [x]
  have hx1 : (x 1 : ℝ) = t := by simp [x]
  have hstep : ∀ i ≤ 0, (x i : ℝ) < (x (i + 1) : ℝ) := by
    intro i hi
    obtain rfl : i = 0 := Nat.le_zero.1 hi
    rw [hx0, hx1]
    exact hst
  have hmesh : ∀ j ≤ 0, (x (j + 1) : ℝ) - (x j : ℝ) ≤ t - s := by
    intro j hj
    obtain rfl : j = 0 := Nat.le_zero.1 hj
    rw [hx0, hx1]
  have hsub : uIcc s t ⊆ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le hst.le, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc hs ht
  let F : C(Icc s t, ℝ) := ⟨fun r ↦ f r, hf.continuous.comp continuous_subtype_val⟩
  refine integral_sq_sub_piecewiseLinearInterpCLM_le hstep hx0 hx1 hmesh hf
    ((SobolevInterval.intervalIntegrable_deriv zero_le_one U _).mono_set hsub)
    ((SobolevInterval.intervalIntegrable_deriv_sq zero_le_one U _).mono_set hsub)
    (fun r hr r' hr' ↦ hfU r ⟨hs.trans hr.1, hr.2.trans ht⟩ r' ⟨hs.trans hr'.1, hr'.2.trans ht⟩)
    (F := F) (fun r ↦ rfl) (fun r ↦ ?_)
  rw [piecewiseLinearInterpCLM_apply_of_mem hstep F le_rfl (by rw [hx0]; exact r.2.1)
    (by rw [hx1]; exact r.2.2), hG r r.2]
  simp only [F, ContinuousMap.coe_mk, hx0, hx1]

/-- **The arclength integral over a sub-segment of a side**, as an interval integral of the
pulled-back function: `∫ F d(edgeMeasure (A + s(B−A)) (A + t(B−A))) = ‖B − A‖ ∫_s^t F(A + r(B−A))`.
-/
theorem integral_edgeMeasure_lineMap {A B : 𝔼₂} {s t : ℝ} (hst : s < t) {F : 𝔼₂ → ℝ}
    (hF : ContinuousOn F (segment ℝ (AffineMap.lineMap A B s) (AffineMap.lineMap A B t))) :
    ∫ x, F x ∂edgeMeasure (AffineMap.lineMap A B s) (AffineMap.lineMap A B t)
      = ‖B - A‖ * ∫ r in s..t, F (AffineMap.lineMap A B r) := by
  rw [integral_edgeMeasure hF]
  have hQP : AffineMap.lineMap A B t - AffineMap.lineMap A B s = (t - s) • (B - A) := by
    simp only [lineMap_eq]
    module
  have hcomp : ∀ r : ℝ, AffineMap.lineMap (AffineMap.lineMap A B s) (AffineMap.lineMap A B t) r
      = AffineMap.lineMap A B ((t - s) * r + s) := by
    intro r
    simp only [lineMap_eq]
    module
  simp_rw [hcomp]
  rw [integral_comp_mul_add (fun r ↦ F (AffineMap.lineMap A B r)) (sub_ne_zero.2 hst.ne') s,
    hQP, norm_smul, Real.norm_eq_abs, abs_of_pos (sub_pos.2 hst)]
  simp only [mul_zero, zero_add, mul_one, sub_add_cancel, smul_eq_mul]
  have hts : t - s ≠ 0 := sub_ne_zero.2 hst.ne'
  field_simp

variable {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω)

/-- The length of an edge of an element is at most the mesh size. -/
theorem norm_vertex_sub_le_meshSize (T : 𝒯.elems) (a b : Fin 3) :
    ‖T.1 b - T.1 a‖ ≤ 𝒯.meshSize := by
  rw [← dist_eq_norm]
  refine (Metric.dist_le_diam_of_mem (𝒯.isCompact_closedK T).isBounded (𝒯.vertex_mem_closedK T b)
    (𝒯.vertex_mem_closedK T a)).trans ?_
  rw [← 𝒯.closure_K, Metric.diam_closure]
  exact 𝒯.diam_le_meshSize T

/-- **A boundary edge on a side, parametrized**: if the edge `[T a, T (a+1)]` lies on the segment
`[A, B]` then its ends are `A + s(B − A)` and `A + t(B − A)` with `0 ≤ s < t ≤ 1`, in one of the
two orientations. -/
theorem exists_param_of_segment_subset {A B : 𝔼₂} (T : 𝒯.elems) (a : Fin 3)
    (h : segment ℝ (T.1 a) (T.1 (a + 1)) ⊆ segment ℝ A B) :
    ∃ s t : ℝ, 0 ≤ s ∧ s < t ∧ t ≤ 1 ∧
      ((T.1 a = AffineMap.lineMap A B s ∧ T.1 (a + 1) = AffineMap.lineMap A B t) ∨
        (T.1 a = AffineMap.lineMap A B t ∧ T.1 (a + 1) = AffineMap.lineMap A B s)) := by
  obtain ⟨s₀, hs₀0, hs₀1, hs₀⟩ := mem_segment_iff'.1 (h (left_mem_segment ℝ _ _))
  obtain ⟨t₀, ht₀0, ht₀1, ht₀⟩ := mem_segment_iff'.1 (h (right_mem_segment ℝ _ _))
  rw [← lineMap_eq] at hs₀ ht₀
  have hne : s₀ ≠ t₀ := fun e ↦ 𝒯.vertex_ne_vertex_add_one T a (by rw [hs₀, ht₀, e])
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact ⟨s₀, t₀, hs₀0, hlt, ht₀1, Or.inl ⟨hs₀, ht₀⟩⟩
  · exact ⟨t₀, s₀, ht₀0, hlt, hs₀1, Or.inr ⟨hs₀, ht₀⟩⟩

/-- The open parameter interval of a sub-segment maps into its open segment. -/
theorem lineMap_mem_openSegment_of_mem_Ioo {A B : 𝔼₂} {s t : ℝ} (hst : s < t) {r : ℝ}
    (hr : r ∈ Ioo s t) :
    AffineMap.lineMap A B r
      ∈ openSegment ℝ (AffineMap.lineMap A B s) (AffineMap.lineMap A B t) := by
  have hts : t - s ≠ 0 := sub_ne_zero.2 hst.ne'
  rw [mem_openSegment_iff']
  refine ⟨(r - s) / (t - s), div_pos (sub_pos.2 hr.1) (sub_pos.2 hst),
    (div_lt_one (sub_pos.2 hst)).2 (sub_lt_sub_right hr.2 s), ?_⟩
  simp only [lineMap_eq]
  rw [show A + t • (B - A) - (A + s • (B - A)) = (t - s) • (B - A) by module, smul_smul,
    div_mul_cancel₀ _ hts]
  module

/-- The length of a sub-segment of a side. -/
theorem norm_lineMap_sub_lineMap (A B : 𝔼₂) {s t : ℝ} (hst : s ≤ t) :
    ‖AffineMap.lineMap A B t - AffineMap.lineMap A B s‖ = (t - s) * ‖B - A‖ := by
  rw [show AffineMap.lineMap A B t - AffineMap.lineMap A B s = (t - s) • (B - A) by
    simp only [lineMap_eq]; module, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hst)]

/-- **The linear interpolant along an edge is the affine interpolant of the edge restriction**:
for two vertices `T b = A + s(B − A)`, `T c = A + t(B − A)` of the element `T` on the side
`[A, B]`, `Π_h v (A + r(B − A)) = v(T b) + (v(T c) − v(T b)) (r − s)/(t − s)` for `r ∈ [s, t]`
(`Triangulation.localInterp_lineMap` for the affine barycentric shape functions). -/
theorem globalInterp_lineMap_side {A B : 𝔼₂} {s t : ℝ} (hst : s < t) (T : 𝒯.elems) (b c : Fin 3)
    (hb : T.1 b = AffineMap.lineMap A B s) (hc : T.1 c = AffineMap.lineMap A B t) (v : 𝔼₂ → ℝ)
    {r : ℝ} (hr : r ∈ Icc s t) :
    𝒯.globalInterp referenceTriangleVertex baryCoord v (AffineMap.lineMap A B r)
      = v (T.1 b) + (v (T.1 c) - v (T.1 b)) * ((r - s) / (t - s)) := by
  have hts : t - s ≠ 0 := sub_ne_zero.2 hst.ne'
  have hpt : AffineMap.lineMap A B r = T.1 b + ((r - s) / (t - s)) • (T.1 c - T.1 b) := by
    rw [hb, hc]
    simp only [lineMap_eq]
    rw [show A + t • (B - A) - (A + s • (B - A)) = (t - s) • (B - A) by module, smul_smul,
      div_mul_cancel₀ _ hts]
    module
  have hmem : AffineMap.lineMap A B r ∈ 𝒯.closedK T := by
    refine 𝒯.segment_subset_closedK T b c ?_
    rw [hpt, mem_segment_iff']
    exact ⟨_, div_nonneg (sub_nonneg.2 hr.1) (sub_nonneg.2 hst.le),
      div_le_one_of_le₀ (sub_le_sub_right hr.2 s) (sub_nonneg.2 hst.le), rfl⟩
  rw [𝒯.globalInterp_eq_of_mem_closedK _ _ 𝒯.isConformingElement_linear T v hmem, hpt,
    𝒯.localInterp_lineMap _ _ baryCoord_lineMap, 𝒯.localInterp_linear_vertex,
    𝒯.localInterp_linear_vertex]
  ring

/-- **The `L²` error of the linear interpolant on a boundary edge lying on a side**: for
`T b = A + s(B − A)`, `T c = A + t(B − A)` and an edge restriction
`r ↦ ũ (A + r(B − A)) ∈ H²(0, 1)` (represented by `U`),
`∫_{[T b, T c]} (ũ − Π_h ũ)² ds ≤ ‖B − A‖ (t − s)⁴ ∫_s^t |U''|²`. -/
theorem integral_sq_sub_globalInterp_edge_le {A B : 𝔼₂} {ũ : 𝔼₂ → ℝ}
    (hũc : ContinuousOn ũ (closure (Ω : Set 𝔼₂))) (U : SobolevInterval 2 0 1)
    (hU : SobolevInterval.fn U =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun r ↦ ũ (AffineMap.lineMap A B r))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1) (T : 𝒯.elems) (b c : Fin 3)
    (hb : T.1 b = AffineMap.lineMap A B s) (hc : T.1 c = AffineMap.lineMap A B t) :
    ∫ x, (ũ x - 𝒯.globalInterp referenceTriangleVertex baryCoord ũ x) ^ 2
        ∂edgeMeasure (T.1 b) (T.1 c)
      ≤ ‖B - A‖ * (t - s) ^ 4 * ∫ r in s..t, SobolevInterval.deriv U (Fin.last 2) r ^ 2 := by
  obtain ⟨f, hf, hae, hftc⟩ := SobolevInterval.exists_contDiff_ae_eq zero_lt_one U
  have hf0 : SobolevInterval.fn U =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] f := by
    rw [← SobolevInterval.deriv_zero U]
    simpa using hae 0
  have hts : t - s ≠ 0 := sub_ne_zero.2 hst.ne'
  -- the parametrization maps `[s, t]` onto the edge, which lies in `Ω̄`
  have hseg : ∀ r ∈ Icc s t, AffineMap.lineMap A B r ∈ segment ℝ (T.1 b) (T.1 c) := by
    intro r hr
    rw [hb, hc, mem_segment_iff']
    refine ⟨(r - s) / (t - s), div_nonneg (sub_nonneg.2 hr.1) (sub_nonneg.2 hst.le),
      div_le_one_of_le₀ (sub_le_sub_right hr.2 s) (sub_nonneg.2 hst.le), ?_⟩
    simp only [lineMap_eq]
    rw [show A + t • (B - A) - (A + s • (B - A)) = (t - s) • (B - A) by module, smul_smul,
      div_mul_cancel₀ _ hts]
    module
  have hcl : ∀ r ∈ Icc s t, AffineMap.lineMap A B r ∈ closure (Ω : Set 𝔼₂) := fun r hr ↦
    𝒯.segment_subset_closure T b c (hseg r hr)
  have hcont : ContinuousOn (fun r ↦ ũ (AffineMap.lineMap A B r)) (Icc s t) :=
    hũc.comp (continuous_lineMap A B).continuousOn hcl
  have hfeq : EqOn f (fun r ↦ ũ (AffineMap.lineMap A B r)) (Icc s t) :=
    eqOn_Icc_of_ae_eq hst hf.continuous.continuousOn hcont
      ((hf0.symm.trans hU).filter_mono (ae_mono (Measure.restrict_mono (Ioo_subset_Ioo hs ht)
        le_rfl)))
  -- the interpolant along the edge
  have hG : ∀ r ∈ Icc s t, 𝒯.globalInterp referenceTriangleVertex baryCoord ũ
      (AffineMap.lineMap A B r) = f s + (f t - f s) * ((r - s) / (t - s)) := by
    intro r hr
    rw [globalInterp_lineMap_side 𝒯 hst T b c hb hc ũ hr, hfeq (left_mem_Icc.2 hst.le),
      hfeq (right_mem_Icc.2 hst.le), hb, hc]
  -- the arclength integral as an interval integral
  have hcP : ContinuousOn (fun x ↦ (ũ x - 𝒯.globalInterp referenceTriangleVertex baryCoord ũ x) ^ 2)
      (segment ℝ (T.1 b) (T.1 c)) :=
    ((hũc.sub (𝒯.continuousOn_globalInterp referenceTriangleVertex baryCoord
      𝒯.isConformingElement_linear (fun i ↦ (contDiff_baryCoord i).continuous) ũ)).pow 2).mono
      (𝒯.segment_subset_closure T b c)
  rw [hb, hc] at hcP ⊢
  rw [integral_edgeMeasure_lineMap hst hcP]
  have hcongr : ∫ r in s..t, (ũ (AffineMap.lineMap A B r)
      - 𝒯.globalInterp referenceTriangleVertex baryCoord ũ (AffineMap.lineMap A B r)) ^ 2
      = ∫ r in s..t, (f r - (f s + (f t - f s) * ((r - s) / (t - s)))) ^ 2 := by
    refine integral_congr fun r hr ↦ ?_
    rw [uIcc_of_le hst.le] at hr
    rw [hfeq hr, hG r hr]
  rw [hcongr, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine integral_sq_sub_affine_le U (by simpa using hf) (fun r hr r' hr' ↦ ?_) hs hst ht
    (G := fun r ↦ f s + (f t - f s) * ((r - s) / (t - s))) (fun r _ ↦ rfl)
  have := hftc r hr r' hr'
  simpa only [iteratedDeriv_one] using this

/-- **The per-edge estimate with the mesh size**: a boundary edge `(T, a)` lying on the side
`[A, B]` has parameters `0 ≤ s < t ≤ 1` on the side, its open parameter interval maps into its
open segment, its length is `(t − s) ‖B − A‖`, and
`∫_e (ũ − Π_h ũ)² ds ≤ h⁴ ‖B − A‖⁻³ ∫_s^t |U''|²` with `h` the mesh size. -/
theorem exists_param_integral_sq_sub_globalInterp_le {A B : 𝔼₂} (hAB : A ≠ B) {ũ : 𝔼₂ → ℝ}
    (hũc : ContinuousOn ũ (closure (Ω : Set 𝔼₂))) (U : SobolevInterval 2 0 1)
    (hU : SobolevInterval.fn U =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun r ↦ ũ (AffineMap.lineMap A B r))
    (T : 𝒯.elems) (a : Fin 3) (h : segment ℝ (T.1 a) (T.1 (a + 1)) ⊆ segment ℝ A B) :
    ∃ s t : ℝ, 0 ≤ s ∧ s < t ∧ t ≤ 1 ∧
      (∀ r ∈ Ioo s t, AffineMap.lineMap A B r ∈ openSegment ℝ (T.1 a) (T.1 (a + 1))) ∧
      ‖T.1 (a + 1) - T.1 a‖ = (t - s) * ‖B - A‖ ∧
      ∫ x, (ũ x - 𝒯.globalInterp referenceTriangleVertex baryCoord ũ x) ^ 2
          ∂edgeMeasure (T.1 a) (T.1 (a + 1))
        ≤ 𝒯.meshSize ^ 4 * ‖B - A‖⁻¹ ^ 3
          * ∫ r in Ioo s t, SobolevInterval.deriv U (Fin.last 2) r ^ 2 := by
  have hBA : 0 < ‖B - A‖ := norm_pos_iff.2 (sub_ne_zero.2 hAB.symm)
  obtain ⟨s, t, hs, hst, ht, hor⟩ := exists_param_of_segment_subset 𝒯 T a h
  refine ⟨s, t, hs, hst, ht, ?_, ?_, ?_⟩
  · intro r hr
    rcases hor with ⟨hb, hc⟩ | ⟨hb, hc⟩
    · rw [hb, hc]
      exact lineMap_mem_openSegment_of_mem_Ioo hst hr
    · rw [hb, hc, openSegment_symm]
      exact lineMap_mem_openSegment_of_mem_Ioo hst hr
  · rcases hor with ⟨hb, hc⟩ | ⟨hb, hc⟩
    · rw [hb, hc, norm_lineMap_sub_lineMap A B hst.le]
    · rw [hb, hc, norm_sub_rev, norm_lineMap_sub_lineMap A B hst.le]
  · have hlen : (t - s) * ‖B - A‖ ≤ 𝒯.meshSize := by
      rcases hor with ⟨hb, hc⟩ | ⟨hb, hc⟩
      · rw [← norm_lineMap_sub_lineMap A B hst.le, ← hb, ← hc]
        exact norm_vertex_sub_le_meshSize 𝒯 T a (a + 1)
      · rw [← norm_lineMap_sub_lineMap A B hst.le, ← hb, ← hc]
        exact norm_vertex_sub_le_meshSize 𝒯 T (a + 1) a
    have hI : ∫ r in Ioo s t, SobolevInterval.deriv U (Fin.last 2) r ^ 2
        = ∫ r in s..t, SobolevInterval.deriv U (Fin.last 2) r ^ 2 := by
      rw [integral_of_le hst.le, integral_Ioc_eq_integral_Ioo]
    have hI0 : 0 ≤ ∫ r in s..t, SobolevInterval.deriv U (Fin.last 2) r ^ 2 :=
      integral_nonneg hst.le fun r _ ↦ sq_nonneg _
    have hcoef : ‖B - A‖ * (t - s) ^ 4 ≤ 𝒯.meshSize ^ 4 * ‖B - A‖⁻¹ ^ 3 := by
      have h4 : ((t - s) * ‖B - A‖) ^ 4 ≤ 𝒯.meshSize ^ 4 :=
        pow_le_pow_left₀ (mul_nonneg (sub_nonneg.2 hst.le) hBA.le) hlen 4
      have e : ‖B - A‖ * (t - s) ^ 4 = ((t - s) * ‖B - A‖) ^ 4 * ‖B - A‖⁻¹ ^ 3 := by
        field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_right h4 (by positivity)
    rw [hI]
    rcases hor with ⟨hb, hc⟩ | ⟨hb, hc⟩
    · exact (integral_sq_sub_globalInterp_edge_le 𝒯 hũc U hU hs hst ht T a (a + 1) hb hc).trans
        (mul_le_mul_of_nonneg_right hcoef hI0)
    · rw [edgeMeasure_symm]
      exact (integral_sq_sub_globalInterp_edge_le 𝒯 hũc U hU hs hst ht T (a + 1) a hc hb).trans
        (mul_le_mul_of_nonneg_right hcoef hI0)

/-- **The `L²(Γ)` error of the linear interpolant on a polygon**: if every boundary edge of `𝒯`
lies on one of the sides `[P k, Q k]` and the restriction of `ũ` to each side is in `H²(0, 1)`
(represented by `Us k`), then

  `∫_Γ (ũ − Π_h ũ)² ds ≤ h⁴ ∑ₖ ‖Q k − P k‖⁻³ |Us k|²_{H²(0,1)}`.

The sum over the boundary edges is grouped by the sides; on one side the parameter intervals of
the edges are pairwise disjoint (their open segments are, by
`Triangulation.openSegment_disjoint_of_isBoundaryEdge`), so the panel estimates add up to the
integral over `(0, 1)`. -/
theorem integral_sq_sub_globalInterp_boundaryMeasure_le {κ : Type*} [Fintype κ]
    {P Q : κ → 𝔼₂} (hPQ : ∀ k, P k ≠ Q k)
    (hside : ∀ (T : 𝒯.elems) (a : Fin 3), 𝒯.IsBoundaryEdge T a →
      ∃ k, segment ℝ (T.1 a) (T.1 (a + 1)) ⊆ segment ℝ (P k) (Q k))
    {ũ : 𝔼₂ → ℝ} (hũc : ContinuousOn ũ (closure (Ω : Set 𝔼₂))) (Us : κ → SobolevInterval 2 0 1)
    (hUs : ∀ k, SobolevInterval.fn (Us k) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun r ↦ ũ (AffineMap.lineMap (P k) (Q k) r)) :
    ∫ x, (ũ x - 𝒯.globalInterp referenceTriangleVertex baryCoord ũ x) ^ 2 ∂𝒯.boundaryMeasure
      ≤ 𝒯.meshSize ^ 4
        * ∑ k, ‖Q k - P k‖⁻¹ ^ 3 * SobolevInterval.seminorm 2 0 1 (Us k) ^ 2 := by
  classical
  choose k hk using hside
  let ke : 𝒯.boundaryEdges → κ := fun e ↦ k e.1.1 e.1.2 (Triangulation.mem_boundaryEdges.1 e.2)
  have hedge := fun e : 𝒯.boundaryEdges ↦
    exists_param_integral_sq_sub_globalInterp_le 𝒯 (hPQ (ke e)) hũc (Us (ke e)) (hUs (ke e))
      e.1.1 e.1.2 (hk e.1.1 e.1.2 (Triangulation.mem_boundaryEdges.1 e.2))
  choose s t hs hst ht hopen _ hbound using hedge
  have hcont2 : ContinuousOn
      (fun x ↦ (ũ x - 𝒯.globalInterp referenceTriangleVertex baryCoord ũ x) ^ 2)
      (closure (Ω : Set 𝔼₂)) :=
    (hũc.sub (𝒯.continuousOn_globalInterp referenceTriangleVertex baryCoord
      𝒯.isConformingElement_linear (fun i ↦ (contDiff_baryCoord i).continuous) ũ)).pow 2
  have hint : ∀ e ∈ 𝒯.boundaryEdges, Integrable
      (fun x ↦ (ũ x - 𝒯.globalInterp referenceTriangleVertex baryCoord ũ x) ^ 2)
      (edgeMeasure (e.1.1 e.2) (e.1.1 (e.2 + 1))) := fun e he ↦
    ((𝒯.boundaryData.memLp_of_continuousOn hcont2 1).integrable le_rfl).mono_measure
      (Triangulation.edgeMeasure_le_boundaryMeasure (Triangulation.mem_boundaryEdges.1 he))
  rw [Triangulation.boundaryMeasure, integral_finsetSum_measure hint, ← Finset.sum_coe_sort]
  refine le_trans (Finset.sum_le_sum fun e _ ↦ hbound e) ?_
  calc ∑ e : 𝒯.boundaryEdges, 𝒯.meshSize ^ 4 * ‖Q (ke e) - P (ke e)‖⁻¹ ^ 3
          * ∫ r in Ioo (s e) (t e), SobolevInterval.deriv (Us (ke e)) (Fin.last 2) r ^ 2
      = ∑ j, ∑ e ∈ Finset.univ.filter (fun e ↦ ke e = j), 𝒯.meshSize ^ 4
          * ‖Q (ke e) - P (ke e)‖⁻¹ ^ 3
          * ∫ r in Ioo (s e) (t e), SobolevInterval.deriv (Us (ke e)) (Fin.last 2) r ^ 2 :=
        (Finset.sum_fiberwise _ ke _).symm
    _ = ∑ j, 𝒯.meshSize ^ 4 * ‖Q j - P j‖⁻¹ ^ 3 * ∑ e ∈ Finset.univ.filter (fun e ↦ ke e = j),
          ∫ r in Ioo (s e) (t e), SobolevInterval.deriv (Us j) (Fin.last 2) r ^ 2 := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun e he ↦ ?_
        rw [(Finset.mem_filter.1 he).2]
    _ ≤ ∑ j, 𝒯.meshSize ^ 4 * ‖Q j - P j‖⁻¹ ^ 3
          * ∫ r in Ioo (0 : ℝ) 1, SobolevInterval.deriv (Us j) (Fin.last 2) r ^ 2 := by
        refine Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine sum_setIntegral_le_of_pairwiseDisjoint _ (fun e _ ↦ measurableSet_Ioo)
          (fun e _ ↦ Ioo_subset_Ioo (hs e) (ht e)) ?_
          ((memLp_two_iff_integrable_sq (Lp.aestronglyMeasurable _)).1 (Lp.memLp _))
          (fun x ↦ sq_nonneg _)
        intro e he e' he' hne
        rw [Finset.mem_coe, Finset.mem_filter] at he he'
        refine Set.disjoint_left.2 fun r hr hr' ↦ ?_
        have h1 := hopen e r hr
        have h2 := hopen e' r hr'
        rw [he.2] at h1
        rw [he'.2] at h2
        exact Set.disjoint_left.1 (Triangulation.openSegment_disjoint_of_isBoundaryEdge
          (Triangulation.mem_boundaryEdges.1 e.2) (Triangulation.mem_boundaryEdges.1 e'.2)
          fun h ↦ hne (Subtype.ext h)) h1 h2
    _ = 𝒯.meshSize ^ 4
          * ∑ j, ‖Q j - P j‖⁻¹ ^ 3 * SobolevInterval.seminorm 2 0 1 (Us j) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [SobolevInterval.seminorm_sq_eq_integral zero_le_one, integral_of_le zero_le_one,
          integral_Ioc_eq_integral_Ioo]
        ring

/-- **The `L²(Γ)` error of the linear interpolant, as the norm of a trace**: for `w ∈ H¹(Ω)` whose
function is `Π_h ũ − ũ`,
`‖γ w‖_{L²(Γ)} ≤ h² √(∑ₖ ‖Q k − P k‖⁻³ |u|²_{H²(Γₖ)})`. -/
theorem norm_traceL_sub_globalInterp_le (hI : 𝒯.InteriorEdgesSubset) {κ : Type*} [Fintype κ]
    {P Q : κ → 𝔼₂} (hPQ : ∀ k, P k ≠ Q k)
    (hside : ∀ (T : 𝒯.elems) (a : Fin 3), 𝒯.IsBoundaryEdge T a →
      ∃ k, segment ℝ (T.1 a) (T.1 (a + 1)) ⊆ segment ℝ (P k) (Q k))
    {ũ : 𝔼₂ → ℝ} (hũc : ContinuousOn ũ (closure (Ω : Set 𝔼₂))) (Us : κ → SobolevInterval 2 0 1)
    (hUs : ∀ k, SobolevInterval.fn (Us k) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun r ↦ ũ (AffineMap.lineMap (P k) (Q k) r))
    {w : SobolevEuclidean 2 1 2 Ω}
    (hw : fn w =ᵐ[volume.restrict (Ω : Set 𝔼₂)]
      𝒯.globalInterp referenceTriangleVertex baryCoord ũ - ũ) :
    ‖(𝒯.traceFamily hI).traceL 2 ENNReal.ofNat_ne_top w‖
      ≤ 𝒯.meshSize ^ 2
        * Real.sqrt (∑ k, ‖Q k - P k‖⁻¹ ^ 3 * SobolevInterval.seminorm 2 0 1 (Us k) ^ 2) := by
  have hcont := 𝒯.continuousOn_globalInterp referenceTriangleVertex baryCoord
    𝒯.isConformingElement_linear (fun j ↦ (contDiff_baryCoord j).continuous) ũ
  have hγ := (𝒯.traceFamily hI).traceL_ae_eq 2 ENNReal.ofNat_ne_top w
    (𝒯.globalInterp referenceTriangleVertex baryCoord ũ - ũ) hw (hcont.sub hũc)
  have hkey := integral_sq_sub_globalInterp_boundaryMeasure_le 𝒯 hPQ hside hũc Us hUs
  have hsq : ‖(𝒯.traceFamily hI).traceL 2 ENNReal.ofNat_ne_top w‖ ^ 2
      ≤ 𝒯.meshSize ^ 4
        * ∑ k, ‖Q k - P k‖⁻¹ ^ 3 * SobolevInterval.seminorm 2 0 1 (Us k) ^ 2 := by
    rw [norm_sq_eq_integral_sq]
    refine le_trans (le_of_eq ?_) hkey
    refine integral_congr_ae ?_
    filter_upwards [hγ] with x hx
    rw [hx, Pi.sub_apply]
    ring
  have hS0 : 0 ≤ ∑ k, ‖Q k - P k‖⁻¹ ^ 3 * SobolevInterval.seminorm 2 0 1 (Us k) ^ 2 :=
    Finset.sum_nonneg fun k _ ↦ by positivity
  calc ‖(𝒯.traceFamily hI).traceL 2 ENNReal.ofNat_ne_top w‖
      = Real.sqrt (‖(𝒯.traceFamily hI).traceL 2 ENNReal.ofNat_ne_top w‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (𝒯.meshSize ^ 4
          * ∑ k, ‖Q k - P k‖⁻¹ ^ 3 * SobolevInterval.seminorm 2 0 1 (Us k) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = _ := by
        rw [Real.sqrt_mul (by positivity),
          show 𝒯.meshSize ^ 4 = (𝒯.meshSize ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]

end EdgeInterpolation


/-! #### The error estimate -/

section Example1144

open MeasureTheory TopologicalSpace EuclideanSpace SobolevMultiIndex

/-- `ℝ²`, locally. -/
local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

/-- The standard basis of `ℝ²`, locally. -/
local notation "𝔅₂" => OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin 2) ℝ)

/-- **Example 11.4.4.** Theorem 11.4.2 (Falk's lemma) applied to the simplified friction problem
(11.1.13) = (11.4.10) of Example 11.1.2 on a polygonal domain `Ω ⊆ ℝ²`, discretized with linear
elements on a regular family of triangulations `{𝒯_h}` without slits
(`Triangulation.InteriorEdgesSubset`), with `V = H¹(Ω)` and `V_h = 𝒯_h.polySpace 2 1` the
continuous piecewise linear functions: for `f ∈ L²(Ω)`, `g > 0`, the solution `u` of (11.4.10)
and the finite element solutions `u_h ∈ V_h`,

  `‖u − u_h‖_{H¹(Ω)} ≤ c(u) h`.

The regularity assumed by the book — `u ∈ H²(Ω)` and `u|_{Γᵢ} ∈ H²(Γᵢ)` on every side — is made
explicit: `U₂ ∈ H²(Ω)` with `toLowerOrderL U₂ = u`, a representative `ũ` continuous on `Ω̄` (the
hypothesis of Theorem 10.3.9), and for every side `[P k, Q k]` of the polygon an element
`Us k ∈ H²(0, 1)` representing `r ↦ ũ (P k + r (Q k − P k))`. The polygon enters as `hside`:
every boundary edge of every `𝒯_h` lies on one of the finitely many sides. The constant is
`c(u) = √(2 K)` with

  `K = (Mν + g Mσ) √(∑ₖ ‖Q k − P k‖⁻³ |u|²_{H²(Γₖ)}) + ‖−Δu + u − f‖_{L²(Ω)} c₀ |u|_{H²(Ω)}
      + ½ (C c₁ |u|_{H²(Ω)})²`,

`c₀`, `c₁` the interpolation constants of `Chapter10.theorem_10_3_9_linear` (where the shape
regularity enters), `C` the norm comparison of `Chapter10.exists_norm_le_sobolevNorm`, and `Mν`,
`Mσ` bounds — uniform in `h`, as they are for a fixed polygon — for `‖∂u/∂ν‖_{L²(Γ_h)}` and
`√(meas Γ_h)`, the surface measure being the one carried by each triangulation.

The proof is the book's: Falk's lemma at `v_h = Π_h ũ`
(`norm_sub_le_of_isVariationalInequalitySolution_of_subset`, the internal-approximation form
since `V_h ⊆ V`), the residual integrated by parts
(`laplaceForm_sub_load_eq_normalTrace_add`, `abs_residual_le`), the interpolation estimates
`‖u − Π_h u‖_{m,Ω} ≤ c h^{2−m} |u|_{2,Ω}` at `m = 0, 1` (`Chapter10.theorem_10_3_9_linear`), and
on the boundary `γ(u − Π_h u) = ũ − Π_h ũ` with
`‖ũ − Π_h ũ‖_{L²(Γ)} ≤ h² √(∑ₖ ‖Q k − P k‖⁻³ |u|²_{H²(Γₖ)})`
(`norm_traceL_sub_globalInterp_le`, the edge bookkeeping). -/
theorem example_11_4_4 {Ω : Opens 𝔼₂} {ι : Type*} {l : Filter ι} {𝒯 : ι → Triangulation Ω}
    (hreg : Chapter10.IsRegularFamily l fun i ↦ Set.range (𝒯 i).K) {H : ℝ}
    (hH : ∀ i, (𝒯 i).meshSize ≤ H) (hIe : ∀ i, (𝒯 i).InteriorEdgesSubset)
    {κ : Type*} [Finite κ] {P Q : κ → 𝔼₂} (hPQ : ∀ k, P k ≠ Q k)
    (hside : ∀ (i : ι) (T : (𝒯 i).elems) (a : Fin 3), (𝒯 i).IsBoundaryEdge T a →
      ∃ k, segment ℝ (T.1 a) (T.1 (a + 1)) ⊆ segment ℝ (P k) (Q k))
    {g : ℝ} (hg : 0 < g) (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼₂)))
    {U₂ : SobolevEuclidean 2 2 2 Ω} {u : SobolevEuclidean 2 1 2 Ω}
    (hU : toLowerOrderL ℝ 𝔅₂ 2 Ω volume (by norm_num : (1 : ℕ) ≤ 2) U₂ = u)
    {ũ : 𝔼₂ → ℝ} (hũ : fn u =ᵐ[volume.restrict (Ω : Set 𝔼₂)] ũ)
    (hũc : ContinuousOn ũ (closure (Ω : Set 𝔼₂))) (hũ2 : MemSobolev ũ 2 2 Ω volume)
    (Us : κ → SobolevInterval 2 0 1)
    (hUs : ∀ k, SobolevInterval.fn (Us k) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun r ↦ ũ (AffineMap.lineMap (P k) (Q k) r))
    {Mν Mσ : ℝ} (hMν : ∀ i, ‖normalTraceL ((𝒯 i).traceFamily (hIe i)) U₂‖ ≤ Mν)
    (hMσ : ∀ i, (eLpNorm (fun _ : 𝔼₂ ↦ (1 : ℝ)) 2 ((𝒯 i).boundaryData).σ).toReal ≤ Mσ)
    (hu : ∀ (i : ι) (v : SobolevEuclidean 2 1 2 Ω),
      Elliptic.load Ω f (v - u) ≤ Elliptic.laplaceForm Ω u (v - u)
        + frictionFunctional (𝒯 i).boundaryData ((𝒯 i).traceFamily (hIe i)) g v
        - frictionFunctional (𝒯 i).boundaryData ((𝒯 i).traceFamily (hIe i)) g u)
    {uh : ι → SobolevEuclidean 2 1 2 Ω}
    (huh : ∀ i, uh i ∈ (𝒯 i).polySpace 2 1 ∧ ∀ vh ∈ (𝒯 i).polySpace 2 1,
      Elliptic.load Ω f (vh - uh i) ≤ Elliptic.laplaceForm Ω (uh i) (vh - uh i)
        + frictionFunctional (𝒯 i).boundaryData ((𝒯 i).traceFamily (hIe i)) g vh
        - frictionFunctional (𝒯 i).boundaryData ((𝒯 i).traceFamily (hIe i)) g (uh i)) :
    ∃ c : ℝ, ∀ i, ‖u - uh i‖ ≤ c * (𝒯 i).meshSize := by
  classical
  have : Fintype κ := Fintype.ofFinite κ
  -- the interpolation constants of Theorem 10.3.9 and the norm comparison
  obtain ⟨c₁, hc₁, hest₁⟩ := Chapter10.theorem_10_3_9_linear (m := 1) le_rfl hreg hH
  obtain ⟨c₀', hc₀', hest₀⟩ := Chapter10.theorem_10_3_9_linear (m := 0) (by norm_num) hreg hH
  obtain ⟨C, hC0, hC⟩ := Chapter10.exists_norm_le_sobolevNorm Ω
  obtain ⟨Su, hSu⟩ : ∃ Su : ℝ, Su = (sobolevSeminorm ũ 2 2 Ω volume).toReal := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ℝ,
      S = ∑ k, ‖Q k - P k‖⁻¹ ^ 3 * SobolevInterval.seminorm 2 0 1 (Us k) ^ 2 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (Mν + g * Mσ) * Real.sqrt S
      + ‖frictionResidualData U₂ f‖ * (c₀' * Su) + 1 / 2 * (C * (c₁ * Su)) ^ 2 := ⟨_, rfl⟩
  have hSu0 : 0 ≤ Su := hSu ▸ ENNReal.toReal_nonneg
  have hSufin : sobolevSeminorm ũ 2 2 Ω volume ≠ ⊤ := hũ2.sobolevSeminorm_ne_top
  refine ⟨Real.sqrt (2 * K), fun i ↦ ?_⟩
  have hh0 : 0 ≤ (𝒯 i).meshSize := (𝒯 i).meshSize_nonneg
  have hMν0 : 0 ≤ Mν := (norm_nonneg _).trans (hMν i)
  have hMσ0 : 0 ≤ Mσ := ENNReal.toReal_nonneg.trans (hMσ i)
  have hK0 : 0 ≤ K := by
    have h1 : 0 ≤ (Mν + g * Mσ) * Real.sqrt S :=
      mul_nonneg (add_nonneg hMν0 (mul_nonneg hg.le hMσ0)) (Real.sqrt_nonneg _)
    have h2 : 0 ≤ ‖frictionResidualData U₂ f‖ * (c₀' * Su) :=
      mul_nonneg (norm_nonneg _) (mul_nonneg hc₀' hSu0)
    have h3 : 0 ≤ 1 / 2 * (C * (c₁ * Su)) ^ 2 := by positivity
    rw [hK]; linarith
  -- the interpolant `Π_h ũ ∈ V_h`
  have hcont := (𝒯 i).continuousOn_globalInterp referenceTriangleVertex baryCoord
    (𝒯 i).isConformingElement_linear (fun j ↦ (contDiff_baryCoord j).continuous) ũ
  have hpoly := (𝒯 i).globalInterp_isPiecewisePoly (𝒯 i).isConformingElement_linear
    baryCoord_eq_eval ũ
  obtain ⟨vh, hvhmem, hvhfn⟩ := (𝒯 i).exists_mem_polySpace 2 hcont hpoly
  have hvhsub : fn (vh - u) =ᵐ[volume.restrict (Ω : Set 𝔼₂)]
      (𝒯 i).globalInterp referenceTriangleVertex baryCoord ũ - ũ := by
    refine (fn_sub vh u).trans ?_
    filter_upwards [hvhfn, hũ] with x h1 h2
    simp only [Pi.sub_apply, h1, h2]
  have hsubfn : fn (u - vh) =ᵐ[volume.restrict (Ω : Set 𝔼₂)]
      ũ - (𝒯 i).globalInterp referenceTriangleVertex baryCoord ũ := by
    refine (fn_sub u vh).trans ?_
    filter_upwards [hvhfn, hũ] with x h1 h2
    simp only [Pi.sub_apply, h1, h2]
  -- the two variational inequalities in operator form, and Falk's lemma
  have hM := frictionBilinForm_isBoundedWith (Ω := Ω)
  have hα := frictionBilinForm_isEllipticWith (Ω := Ω)
  have hmono := Chapter08.stronglyMonotone_toOperator hM hα
  have hlip := Chapter08.lipschitzWith_toOperator zero_le_one hM
  have huVI : IsVariationalInequalitySolution
      (BilinForm.toOperator (frictionBilinForm (Ω := Ω)) hM)
      (frictionFunctional (𝒯 i).boundaryData ((𝒯 i).traceFamily (hIe i)) g)
      (SesqForm.rieszRep (Elliptic.load Ω f)) univ u := by
    rw [Chapter11.isVariationalInequalitySolution_toOperator_iff]
    exact ⟨mem_univ u, fun v _ ↦ hu i v⟩
  have huhVI : IsVariationalInequalitySolution
      (BilinForm.toOperator (frictionBilinForm (Ω := Ω)) hM)
      (frictionFunctional (𝒯 i).boundaryData ((𝒯 i).traceFamily (hIe i)) g)
      (SesqForm.rieszRep (Elliptic.load Ω f))
      ((𝒯 i).polySpace 2 1 : Set (SobolevEuclidean 2 1 2 Ω)) (uh i) := by
    rw [Chapter11.isVariationalInequalitySolution_toOperator_iff]
    exact ⟨(huh i).1, fun v hv ↦ (huh i).2 v hv⟩
  have hfalk := norm_sub_le_of_isVariationalInequalitySolution_of_subset (c := 1) (L := 1)
    one_pos hmono hlip huVI huhVI (mem_univ _) hvhmem
  simp only [BilinForm.inner_toOperator, BilinForm.inner_rieszRep, frictionBilinForm_apply]
    at hfalk
  -- the residual at `v_h = Π_h ũ`
  have hres := abs_residual_le ((𝒯 i).traceFamily (hIe i)) hg.le hU f vh
  -- the boundary error
  have hT := norm_traceL_sub_globalInterp_le (𝒯 i) (hIe i) hPQ (hside i) hũc Us hUs hvhsub
  rw [← hS] at hT
  -- the `L²(Ω)` error
  have hL2 : ‖weakDeriv (vh - u) 0‖ ≤ c₀' * (𝒯 i).meshSize ^ 2 * Su := by
    have hest := hest₀ i ũ hũ2 hũc
    simp only [Nat.sub_zero] at hest
    have hnorm : ‖weakDeriv (vh - u) 0‖
        = (eLpNorm (fn (vh - u)) 2 (volume.restrict (Ω : Set 𝔼₂))).toReal := Lp.norm_def _
    rw [hnorm, eLpNorm_congr_ae hvhsub, eLpNorm_sub_comm, hSu]
    exact toReal_le_of_le_ofReal_mul (by positivity) hSufin
      ((eLpNorm_le_sobolevNorm_zero (memSobolev_sub_globalInterp_linear (𝒯 i) hũ2)).trans hest)
  -- the `H¹(Ω)` error
  have hH1 : ‖u - vh‖ ≤ C * (c₁ * (𝒯 i).meshSize * Su) := by
    have h1 := hC (u - vh)
    rw [sobolevNorm_congr_ae hsubfn] at h1
    have hest := hest₁ i ũ hũ2 hũc
    simp only [Nat.add_one_sub_one, pow_one] at hest
    rw [hSu]
    exact h1.trans (mul_le_mul_of_nonneg_left
      (toReal_le_of_le_ofReal_mul (by positivity) hSufin hest) hC0)
  -- assemble
  have hR : Elliptic.laplaceForm Ω u (vh - u)
      + frictionFunctional (𝒯 i).boundaryData ((𝒯 i).traceFamily (hIe i)) g vh
      - frictionFunctional (𝒯 i).boundaryData ((𝒯 i).traceFamily (hIe i)) g u
      - Elliptic.load Ω f (vh - u)
      ≤ (Mν + g * Mσ) * ((𝒯 i).meshSize ^ 2 * Real.sqrt S)
        + ‖frictionResidualData U₂ f‖ * (c₀' * (𝒯 i).meshSize ^ 2 * Su) := by
    refine (le_abs_self _).trans (hres.trans (add_le_add ?_ ?_))
    · exact mul_le_mul (add_le_add (hMν i) (mul_le_mul_of_nonneg_left (hMσ i) hg.le)) hT
        (norm_nonneg _) (add_nonneg hMν0 (mul_nonneg hg.le hMσ0))
    · exact mul_le_mul_of_nonneg_left hL2 (norm_nonneg _)
  have hsq : ‖u - vh‖ ^ 2 ≤ (C * (c₁ * (𝒯 i).meshSize * Su)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hH1 2
  have hmain : 1 / 2 * ‖u - uh i‖ ^ 2 ≤ K * (𝒯 i).meshSize ^ 2 := by
    refine hfalk.trans ?_
    calc _ ≤ ((Mν + g * Mσ) * ((𝒯 i).meshSize ^ 2 * Real.sqrt S)
          + ‖frictionResidualData U₂ f‖ * (c₀' * (𝒯 i).meshSize ^ 2 * Su))
          + 1 ^ 2 / (2 * 1) * (C * (c₁ * (𝒯 i).meshSize * Su)) ^ 2 :=
          add_le_add hR (mul_le_mul_of_nonneg_left hsq (by norm_num))
      _ = K * (𝒯 i).meshSize ^ 2 := by rw [hK]; ring
  have hfin : ‖u - uh i‖ ^ 2 ≤ 2 * K * (𝒯 i).meshSize ^ 2 := by linarith
  calc ‖u - uh i‖ = Real.sqrt (‖u - uh i‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (2 * K * (𝒯 i).meshSize ^ 2) := Real.sqrt_le_sqrt hfin
    _ = Real.sqrt (2 * K) * (𝒯 i).meshSize := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hh0]

end Example1144

end AtkinsonHan.Chapter11
