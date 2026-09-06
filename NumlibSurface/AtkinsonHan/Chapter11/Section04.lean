import Numlib.Variational.Inequality.Approximation
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
* `theorem_11_4_7` — the error bound (11.4.27) when the discrete functional dominates `j`.

`residual` is the book's `R(v, w)` of the display preceding (11.4.7), with the functional at the
two arguments kept separate so that the same definition serves the `R_h` of (11.4.27).

## Deviations from the book

* **The estimates are squared.**  Falk's lemma is `(c₀/2) ‖u - u_h‖² ≤ R(v, u_h) + R(v_h, u) +
  (M²/(2c₀)) ‖u - v_h‖²`, which is what its proof establishes; the book's square-rooted form is
  `theorem_11_4_2_of_subset`, with the constant `max (M/c₀) √(2/c₀)` written out.
* **The weak-closedness hypothesis of Theorem 11.4.1 is indexed by an arbitrary reindexing
  `σ : ℕ → ℕ`**, because the proof runs through `tendsto_of_subseq_tendsto` and so tests the
  hypothesis along a subsequence.  Boundedness of the discrete solutions is not a separate
  hypothesis: it falls out of Falk's lemma at `v = u` together with an affine minorant of `j`.
* **Exercise 11.4.2 asks for the subspaces to be nested.**  "The union of the `V_h` is dense" does
  not by itself produce, for each `n`, a point of `V_h n` near `u`; monotonicity does, and the
  approximating sequence is then the sequence of best approximations, whose errors are antitone.

## Not formalized

Theorem 11.4.6, the convergence of the method of numerical integration (11.4.25): see the group
file for the obstruction, which is that the backbone's convergence theorem carries **one**
functional `j` shared by the continuous and the discrete problem, while Theorem 11.4.6 varies it.
Theorem 11.4.5 and Exercise 11.4.4 (the Lagrange-multiplier form of the simplified friction
problem) live on `H^{1/2}(Γ)`; Examples 11.4.3 and 11.4.4 and the analysis of (11.4.29) are finite
element interpolation estimates on a polygonal domain; Exercises 11.4.1 and 11.4.5 name a domain
as well.
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

/-- The book's (11.3.1) in the shape the backbone takes it. -/
private theorem isStronglyMonotoneWith_of (hmono : Chapter05.StronglyMonotoneWith A c₀) :
    IsStronglyMonotoneWith ℝ A c₀ := Chapter05.stronglyMonotoneWith_iff.1 hmono

/-- The constant `c` of the square-rooted error bounds (11.4.7) and (11.4.27). -/
private noncomputable def falkConst (c₀ M : ℝ) : ℝ := max (M / c₀) (Real.sqrt (2 / c₀))

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
  tendsto_of_isVariationalInequalitySolution hc₀ (isStronglyMonotoneWith_of hmono)
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
is Céa's lemma, which this surface has as `AtkinsonHan.Chapter09.theorem_9_1_3`. -/
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
    have h := norm_sub_le_of_isVariationalInequalitySolution hc₀ (isStronglyMonotoneWith_of hmono)
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
    (isStronglyMonotoneWith_of hmono) ((Chapter05.lipschitzWith_toNNReal_iff hM).1 hlip) hu huh
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
  exact tendsto_of_isVariationalInequalitySolution_of_subset hc₀ (isStronglyMonotoneWith_of hmono)
    ((Chapter05.lipschitzWith_toNNReal_iff hM).1 hlip) (fun n => subset_univ _) hjc.continuousOn hu
    huh hwmem hwlim

/-! ### Exercise 11.4.3: the regularized problem -/

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
  norm_sub_le_of_regularization hc₀ (isStronglyMonotoneWith_of hmono) hu hueps hreg

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
    (isStronglyMonotoneWith_of hmono) ((Chapter05.lipschitzWith_toNNReal_iff hM).1 hlip) hu huh
    (mem_univ uh) (hjle uh huh.1) vh.2
  simp only [residual]
  linarith

end

end AtkinsonHan.Chapter11
