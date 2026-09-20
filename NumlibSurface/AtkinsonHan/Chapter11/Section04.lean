import Numlib.Analysis.Convex.Continuity
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
  set `discreteObstacleSet` (`K_h ⊄ K`), `Π_h u ∈ K_h` and `max (u_h, ψ) ∈ K`.

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

## Not formalized

Theorem 11.4.5 and Exercise 11.4.4 (the Lagrange-multiplier form of the simplified friction
problem) live on `H^{1/2}(Γ)`; Example 11.4.4 and the analysis of (11.4.29) need the trace, the
surface measure on `Γ` and Green's formula on a polygon (`notes/frontier.md` blocker 2);
Exercises 11.4.1 and 11.4.5 name a domain as well.
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

end AtkinsonHan.Chapter11
