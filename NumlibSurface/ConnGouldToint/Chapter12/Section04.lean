/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Constrained
import NumlibSurface.ConnGouldToint.Chapter03.Section01
import NumlibSurface.ConnGouldToint.Chapter12.Section03
import NumlibSurface.ConnGouldToint.Chapter06.Section06

/-!
# Conn, Gould and Toint, Section 12.4: Lagrangian models on an identified face

This module formalizes the analysis of Section 12.4 of [conn2000trust] once the active set has been
identified. The constraints are written as $c_i(x) \ge 0$, and the active set at $x$ is
$\mathcal{A}(x) = \{i : c_i(x) = 0\}$. For a model $m$ and multipliers $y$ that vanish off
$\mathcal{A}(x)$, the fixed-multiplier Lagrangian model is $L(z) = m(z) - \sum_i y_i c_i(z)$. It
agrees with $m$ at every point with the same active set as $x$. When the multiplier term is the
normal component of $-\nabla f(x)$, the derivative of $L$ at $x$ is minus the tangent component
$P_{T(x)}[-\nabla f(x)]$, as in (12.4.1). Curvature of $L$ along the step then bounds the step by
the tangent linear decrease (Lemmas 12.4.1 and 12.4.2), which gives convergence of the iterates to a
strict minimizer on the face (Theorem 12.4.3), a quadratic model decrease (Lemma 12.4.4) and
eventually very successful iterations (Theorem 12.4.5). The last part treats steps of negative
curvature along the projected ray $t \mapsto P_C[x + t u]$ (Theorem 12.4.6). The proofs use the
projections of `Numlib.Optimization.ModelBased.ProjectedPath` and the Lagrangian of
`Numlib.Optimization.Constrained`.

## Main definitions

* Equation (12.4.3), `ConnGouldToint.Chapter12.faceLagrangianModel`: the fixed-multiplier model
  $m(z) - \sum_i y_i c_i(z)$.
* Equation (12.4.14), `ConnGouldToint.Chapter12.ProjectedEigenTrialAccepted`: the acceptance test of
  a projected negative-curvature trial, with the corrected sign.
* Equation (12.4.16), `ConnGouldToint.Chapter12.activeFaceBoundaryDistance`: the distance from $x$
  to the relative frontier of the feasible part of the active equality locus.

## Main results

* Equation (12.4.1),
  `ConnGouldToint.Chapter12.fderiv_faceLagrangianModel_eq_tangent_of_normal_projection`: if the
  multiplier term is the normal projection of $-\nabla f(x)$, then $DL(x)v = -\langle
  P_{T(x)}[-\nabla f(x)], v \rangle$.
* Equations (12.4.2)–(12.4.3), `ConnGouldToint.Chapter12.faceLagrangianModel_eq_of_active`: at a
  point with the active set of $x$, the Lagrangian model equals the model.
* Lemma 12.4.1, `ConnGouldToint.Chapter12.lemma_12_4_1`: on a fixed face, $m(x + s) = m(x) - \langle
  P_{T(x)}[-\nabla f(x)], s \rangle + \frac12 \nabla^2 L(x + ts)[s, s]$ for some $t \in (0, 1]$.
* Lemma 12.4.2, `ConnGouldToint.Chapter12.lemma_12_4_2`: positive curvature of $L$ on the step
  segment and model decrease give $\varepsilon \|s\|^2 \le 2 \langle P_{T(x)}[-\nabla f(x)], s
  \rangle$.
* Theorem 12.4.3, `ConnGouldToint.Chapter12.theorem_12_4_3`: a run with a subsequence converging to
  a strict local minimizer on a closed face, which it cannot leave near that point, and with small
  steps near that point, converges to it.
* Lemma 12.4.4, `ConnGouldToint.Chapter12.lemma_12_4_4`: a feasible extension of the step direction
  and AA.1b give a model decrease of order $\|s\|^2$.
* Theorem 12.4.5, `ConnGouldToint.Chapter12.theorem_12_4_5`: Hessian agreement on the trial segments
  and a quadratic model decrease make every late iteration very successful and keep the radii
  bounded away from zero.
* Equation (12.4.16), `ConnGouldToint.Chapter12.activeFaceBoundaryDistance_pos`: the face clearance
  of a feasible point is positive.
* Theorem 12.4.6, `ConnGouldToint.Chapter12.theorem_12_4_6`: the backtracking search along a
  projected negative-curvature ray stops, with a decrease proportional to $-\tau$.
* Equations (12.4.19)–(12.4.22), `ConnGouldToint.Chapter12.projectedRay_taylor_upper_of_face`: a
  Taylor upper bound for the model at a projected trial on the face, with a cubic remainder.

## Deviations from the source

* **Reading.** The Lagrangian derivative identifies the tangent projection with explicit agreement
  and multiplier hypotheses. See `ConnGouldToint.Chapter12.fderiv_faceLagrangianModel_eq_tangent`,
  `ConnGouldToint.Chapter12.fderiv_faceLagrangianModel_eq_tangent_of_normal_projection`.
* **Reading.** The face Taylor and step estimates use supported multipliers and give a
  zero-step-safe product inequality. See `ConnGouldToint.Chapter12.lemma_12_4_1`,
  `ConnGouldToint.Chapter12.lemma_12_4_2`.
* **Reading.** The full-convergence theorem makes identified-face trapping and small local steps
  explicit. See `ConnGouldToint.Chapter12.theorem_12_4_3`,
  `ConnGouldToint.Chapter12.theorem_12_4_3_of_lagrangian`.
* **Reading.** The decrease estimate assumes a uniform feasible step extension and gives a
  sufficient affine-face condition. See
  `ConnGouldToint.Chapter12.extendStep_mem_of_linear_active_face`,
  `ConnGouldToint.Chapter12.lemma_12_4_4`.
* **Reading.** The model agreement estimate is assumed along the entire trial segments. See
  `ConnGouldToint.Chapter12.theorem_12_4_5`.
* **Reading.** The distance uses the frontier relative to the active equality locus and allows
  infinite distance. See `ConnGouldToint.Chapter12.activeEqualityLocus`,
  `ConnGouldToint.Chapter12.activeFaceBoundaryDistance`,
  `ConnGouldToint.Chapter12.activeFaceBoundaryDistance_pos`.
* **Correction.** The eigenpoint test corrects the sign of the negative-curvature term. See
  `ConnGouldToint.Chapter12.ProjectedEigenTrialAccepted`,
  `ConnGouldToint.Chapter12.eigenTrial_printed_sign_counterexample`.
* **Correction.** The accepted eigenpoint bound uses positive curvature magnitude and explicit
  projection and face-radius control. See
  `ConnGouldToint.Chapter12.projectedRay_taylor_upper_of_face`,
  `ConnGouldToint.Chapter12.theorem_12_4_6`.
* **Theorem 12.4.3** (reading). The trapping of the iterates on the identified face near the limit
  and the small steps near the limit are explicit hypotheses. See
  `ConnGouldToint.Chapter12.theorem_12_4_3`.
* **Lemma 12.4.4** (reading). The feasible extension of the step direction by a uniform length is an
  explicit hypothesis. See `ConnGouldToint.Chapter12.lemma_12_4_4`.
* **Theorem 12.4.5** (reading). The Hessian agreement (12.4.7) is assumed on the trial segments. See
  `ConnGouldToint.Chapter12.theorem_12_4_5`.
* **Equation (12.4.14)** (correction). The printed test has the sign that accepts a strict model
  increase at negative curvature. The test here requires a decrease. See
  `ConnGouldToint.Chapter12.ProjectedEigenTrialAccepted` and
  `ConnGouldToint.Chapter12.eigenTrial_printed_sign_counterexample`.
* **Equation (12.4.16)** (reading). The distance uses the frontier relative to the active equality
  locus, and it is infinite when that frontier is empty. See
  `ConnGouldToint.Chapter12.activeFaceBoundaryDistance`.
* **Theorem 12.4.6** (correction). The decrease bound uses the corrected sign of (12.4.14) and
  includes the face radius. See `ConnGouldToint.Chapter12.theorem_12_4_6`.
-/

open Set Optimization Filter Topology
open scoped RealInnerProductSpace

namespace ConnGouldToint.Chapter12

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]

/-- **Equation (12.4.3)** of [conn2000trust]. For a model $m : E \to \mathbb{R}$, constraints
$c_i : E \to \mathbb{R}$ written as $c_i(x) \ge 0$, and multipliers $y \in \mathbb{R}^\iota$,
the **fixed-multiplier Lagrangian model** is
$$L(x) = m(x) - \sum_i y_i\, c_i(x).$$

The definition is `Constrained.lagrangian` with the multipliers $-y_i$, because the constraints
are inequalities $c_i \ge 0$. -/
def faceLagrangianModel (m : E → ℝ) (c : ι → E → ℝ) (y : ι → ℝ) (x : E) : ℝ :=
  Constrained.lagrangian m c x (fun i ↦ -y i)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- **Equations (12.4.2)–(12.4.3)** of [conn2000trust]. Let $x, z \in E$ have the same active set,
$\mathcal{A}(z) = \mathcal{A}(x)$, and let $y_i = 0$ for every $i \notin \mathcal{A}(x)$. Then
the Lagrangian model agrees with the model at $z$: $L(z) = m(z)$. -/
theorem faceLagrangianModel_eq_of_active {m : E → ℝ} {c : ι → E → ℝ} {y : ι → ℝ}
    {x z : E} (hA : activeConstraintSet c z = activeConstraintSet c x)
    (hy : ∀ i ∉ activeConstraintSet c x, y i = 0) :
    faceLagrangianModel m c y z = m z := by
  unfold faceLagrangianModel Constrained.lagrangian
  suffices h : (∑ i, -y i * c i z) = 0 by rw [h, add_zero]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i ∈ activeConstraintSet c x
  · have hz : c i z = 0 := show i ∈ activeConstraintSet c z by rwa [hA]
    rw [hz, mul_zero]
  · rw [hy i hi, neg_zero, zero_mul]

private theorem exists_affine_ray_taylor {L : E → ℝ} (hL : ContDiff ℝ 2 L) (x s : E) :
    ∃ t ∈ Ioc (0 : ℝ) 1,
      L (x + s) = L x + fderiv ℝ L x s +
        (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ L) (x + t • s) s s := by
  let ray (t : ℝ) := L (x + t • s)
  have hray : ContDiff ℝ 2 ray := hL.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hderiv (t : ℝ) : deriv ray t = fderiv ℝ L (x + t • s) s :=
    ((hL.differentiable (by norm_num) _).hasDerivAt_comp_add_smul).deriv
  have hderiv₂ (t : ℝ) : iteratedDeriv 2 ray t = fderiv ℝ (fderiv ℝ L) (x + t • s) s s := by
    have hD : ContDiff ℝ 1 (fderiv ℝ L) := hL.fderiv_right (by norm_num)
    have hd := ((hD.differentiable (by norm_num) (x + t • s)).hasDerivAt_comp_add_smul).clm_apply
      (hasDerivAt_const t s)
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one, funext hderiv]
    simpa only [map_zero, add_zero] using hd.deriv
  have h01 : (0 : ℝ) ≠ 1 := by norm_num
  obtain ⟨t, ht, h⟩ := exists_taylorWithinEval_add_iteratedDeriv_mul
    (n := 1) h01 hray.contDiffOn
  rw [taylorWithinEval_eq_sum_of_contDiffAt h01 (hray.contDiffAt.of_le (by norm_num)),
    Finset.sum_range_succ, Finset.sum_range_one, iteratedDeriv_zero, iteratedDeriv_one,
    hderiv, hderiv₂] at h
  have ht' : t ∈ Ioo (0 : ℝ) 1 := by simpa only [uIoo_of_le zero_le_one] using ht
  refine ⟨t, ⟨ht'.1, ht'.2.le⟩, ?_⟩
  norm_num [ray] at h
  linarith only [h]

variable [CompleteSpace E]

/-- **Equation (12.4.1)** of [conn2000trust]. Let $E$ be a real Hilbert space, let $m$ and every
$c_i$ be differentiable at $x$, and let $Dm(x) = Df(x)$. Write $T(x)$ and $N(x)$ for the tangent
and normal cones of $C$ at $x$, and $P_K$ for the projection onto a closed convex cone $K$.
Suppose that
$$P_{N(x)}[-\nabla f(x)] = -\sum_i y_i \nabla c_i(x) \quad\text{and}\quad P_{T(x)}[-\nabla
  f(x)] + P_{N(x)}[-\nabla f(x)] = -\nabla f(x).$$
Then for every $v \in E$ the Lagrangian model `ConnGouldToint.Chapter12.faceLagrangianModel`
satisfies
$$DL(x)\, v = -\langle P_{T(x)}[-\nabla f(x)], v \rangle.$$

The cones are `Optimization.tangentDirections` and `Optimization.normalDirections`, and the
projections are `bestApprox`. The second hypothesis is Moreau's decomposition;
`ConnGouldToint.Chapter12.fderiv_faceLagrangianModel_eq_tangent_of_normal_projection` derives
it.

**Reading.** The derivative formula assumes explicit model-gradient agreement and a representation
of the normal projection by constraint multipliers. One version assumes Moreau decomposition, while
the companion applies it to the cones.
-/
theorem fderiv_faceLagrangianModel_eq_tangent {C : Set E} {m f : E → ℝ}
    {c : ι → E → ℝ} {y : ι → ℝ} {x : E}
    (hm : DifferentiableAt ℝ m x) (hc : ∀ i, DifferentiableAt ℝ (c i) x)
    (hmatch : fderiv ℝ m x = fderiv ℝ f x)
    (hnormal : bestApprox (normalDirections C x) (-gradient f x) =
      -∑ i, y i • gradient (c i) x)
    (hmoreau : bestApprox (tangentDirections C x) (-gradient f x) +
      bestApprox (normalDirections C x) (-gradient f x) = -gradient f x)
    (v : E) :
    fderiv ℝ (faceLagrangianModel m c y) x v =
      -⟪bestApprox (tangentDirections C x) (-gradient f x), v⟫ := by
  have hd := (Constrained.lagrangian_hasFDerivAt hm.hasFDerivAt
    (fun i ↦ (hc i).hasFDerivAt) (fun i ↦ -y i)).fderiv
  unfold faceLagrangianModel
  rw [hd, add_apply, sum_apply, hmatch, ← inner_gradient_left]
  have h := congrArg (fun w : E ↦ ⟪w, v⟫) hmoreau
  rw [hnormal, inner_add_left, inner_neg_left, sum_inner, inner_neg_left] at h
  simp only [smul_apply, smul_eq_mul, ← inner_gradient_left, neg_mul]
  rw [Finset.sum_neg_distrib]
  simp only [real_inner_smul_left] at h
  linarith only [h]

/-- **Equation (12.4.1)** of [conn2000trust]. Let $E$ be a real Hilbert space, let $m$ and every
$c_i$ be differentiable at $x$, and let $Dm(x) = Df(x)$. If the projection of $-\nabla f(x)$
onto the normal cone $N(x)$ of $C$ at $x$ is $-\sum_i y_i \nabla c_i(x)$, then for every
$v \in E$
$$DL(x)\, v = -\langle P_{T(x)}[-\nabla f(x)], v \rangle,$$
where $L$ is the Lagrangian model `ConnGouldToint.Chapter12.faceLagrangianModel` and $P_{T(x)}$
is the projection onto the tangent cone of $C$ at $x$.

The tangent component follows from Moreau's decomposition (3.1.7) of $-\nabla f(x)$ into its
projections onto the polar cones $T(x)$ and $N(x)$.

**Reading.** The derivative formula assumes explicit model-gradient agreement and a representation
of the normal projection by constraint multipliers. One version assumes Moreau decomposition, while
the companion applies it to the cones.
-/
theorem fderiv_faceLagrangianModel_eq_tangent_of_normal_projection {C : Set E}
    {m f : E → ℝ} {c : ι → E → ℝ} {y : ι → ℝ} {x : E}
    (hm : DifferentiableAt ℝ m x) (hc : ∀ i, DifferentiableAt ℝ (c i) x)
    (hmatch : fderiv ℝ m x = fderiv ℝ f x)
    (hnormal : bestApprox (normalDirections C x) (-gradient f x) =
      -∑ i, y i • gradient (c i) x) (v : E) :
    fderiv ℝ (faceLagrangianModel m c y) x v =
      -⟪bestApprox (tangentDirections C x) (-gradient f x), v⟫ :=
  fderiv_faceLagrangianModel_eq_tangent hm hc hmatch hnormal
    (Chapter03.moreau_normal_tangent C x (-gradient f x)).1.symm v

/-- **Lemma 12.4.1** of [conn2000trust]. Let $E$ be a real Hilbert space, let $x, s \in E$ with
$\mathcal{A}(x + s) = \mathcal{A}(x)$, and let $y_i = 0$ for every $i \notin \mathcal{A}(x)$.
Suppose that the Lagrangian model $L$ of (12.4.3) is twice continuously differentiable and that
$DL(x)\, s = -\langle P_{T(x)}[-\nabla f(x)], s \rangle$. Then there is $t \in (0, 1]$ with
$$m(x + s) = m(x) - \langle P_{T(x)}[-\nabla f(x)], s \rangle + \tfrac12 \nabla^2 L(x + ts)[s,
  s].$$

The derivative hypothesis is the identity (12.4.1); see
`ConnGouldToint.Chapter12.fderiv_faceLagrangianModel_eq_tangent_of_normal_projection`. The proof
applies Taylor's theorem to $L$ on the segment and uses $L = m$ at $x$ and $x + s$.

**Reading.** The Taylor expansion and step bound take equal endpoint active sets, supported
multipliers, and the projected derivative identity directly. The step bound separates a product
inequality valid also at zero from a quotient for a nonzero step.
-/
theorem lemma_12_4_1 {C : Set E} {m f : E → ℝ} {c : ι → E → ℝ} {y : ι → ℝ} {x s : E}
    (hA : activeConstraintSet c (x + s) = activeConstraintSet c x)
    (hy : ∀ i ∉ activeConstraintSet c x, y i = 0)
    (hL : ContDiff ℝ 2 (faceLagrangianModel m c y))
    (hgrad : fderiv ℝ (faceLagrangianModel m c y) x s =
      -⟪bestApprox (tangentDirections C x) (-gradient f x), s⟫) :
    ∃ t ∈ Ioc (0 : ℝ) 1, m (x + s) =
      m x - ⟪bestApprox (tangentDirections C x) (-gradient f x), s⟫ +
        (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ (faceLagrangianModel m c y)) (x + t • s) s s := by
  obtain ⟨t, ht, h⟩ := exists_affine_ray_taylor hL x s
  rw [faceLagrangianModel_eq_of_active hA hy, faceLagrangianModel_eq_of_active rfl hy, hgrad] at h
  exact ⟨t, ht, by simpa only [sub_eq_add_neg] using h⟩

/-- **Lemma 12.4.2** of [conn2000trust]. Let the hypotheses of Lemma 12.4.1 hold for $x$ and $s$,
let $\varepsilon > 0$, let $m(x + s) \le m(x)$, and suppose that $\varepsilon \|s\|^2 \le
\nabla^2 L(x + ts)[s, s]$ for every $t \in (0, 1]$. Put $\ell = \langle P_{T(x)}[-\nabla f(x)],
s \rangle$. Then
$$\varepsilon \|s\|^2 \le 2 \ell,$$
and, if $s \neq 0$, $\|s\| \le 2 \ell / (\varepsilon \|s\|)$.

The product inequality also covers the zero step. The quotient form for $s \neq 0$ is (12.4.5).

**Reading.** The Taylor expansion and step bound take equal endpoint active sets, supported
multipliers, and the projected derivative identity directly. The step bound separates a product
inequality valid also at zero from a quotient for a nonzero step.
-/
theorem lemma_12_4_2 {C : Set E} {m f : E → ℝ} {c : ι → E → ℝ} {y : ι → ℝ} {x s : E}
    (hA : activeConstraintSet c (x + s) = activeConstraintSet c x)
    (hy : ∀ i ∉ activeConstraintSet c x, y i = 0)
    (hL : ContDiff ℝ 2 (faceLagrangianModel m c y))
    (hgrad : fderiv ℝ (faceLagrangianModel m c y) x s =
      -⟪bestApprox (tangentDirections C x) (-gradient f x), s⟫)
    {ε : ℝ} (hε : 0 < ε) (hdec : m (x + s) ≤ m x)
    (hcurv : ∀ t ∈ Ioc (0 : ℝ) 1, ε * ‖s‖ ^ 2 ≤
      fderiv ℝ (fderiv ℝ (faceLagrangianModel m c y)) (x + t • s) s s) :
    let l := ⟪bestApprox (tangentDirections C x) (-gradient f x), s⟫
    ε * ‖s‖ ^ 2 ≤ 2 * l ∧ (s ≠ 0 → ‖s‖ ≤ (2 * l) / (ε * ‖s‖)) := by
  obtain ⟨t, ht, h⟩ := lemma_12_4_1 hA hy hL hgrad
  have hb := hcurv t ht
  dsimp only
  have hprod : ε * ‖s‖ ^ 2 ≤ 2 * ⟪bestApprox (tangentDirections C x) (-gradient f x), s⟫ := by
    linarith only [h, hb, hdec]
  exact ⟨hprod, fun hs ↦ (le_div_iff₀ (mul_pos hε (norm_pos_iff.mpr hs))).mpr
    (by nlinarith only [hprod])⟩

omit [Fintype ι] [CompleteSpace E] in
/-- **Theorem 12.4.3** of [conn2000trust], identified-face form. Let $E$ be a real inner product
space in which closed balls are compact, and consider a run of the basic trust-region algorithm
(Algorithm 6.1.1) for a continuous objective $f$. Let $F \subseteq E$ be closed, and let a
subsequence $x_{j(k)}$ converge to $z$. Let $\rho > 0$ and suppose that

* $f(z) < f(y)$ for every $y \in F$ with $0 < \operatorname{dist}(y, z) \le \rho$;
* eventually, $\operatorname{dist}(x_k, z) \le \rho$ implies $x_k \in F$;
* for every $\varepsilon > 0$ there is $R > 0$ such that, eventually,
  $\operatorname{dist}(x_k, z) < R$ implies $\operatorname{dist}(x_{k+1}, x_k) \le \varepsilon$.

Then the whole sequence converges: $x_k \to z$.

**Reading.** The statement makes the local trapping on the identified face explicit: the
iterates near $z$ lie on the face $F$, $z$ is a strict minimizer of $f$ on $F$ near $z$, and the
steps are small near $z$. `ConnGouldToint.Chapter12.theorem_12_4_3_of_lagrangian` derives the
small steps from the curvature of the Lagrangian model.

The argument uses that the objective values of the run do not increase.

**Reading.** Whole-sequence convergence assumes late nearby iterates lie on the identified closed
face and accepted steps become small near the limit. A companion gets the small-step condition from
explicit Lagrangian curvature and tangent-gradient control.
-/
theorem theorem_12_4_3 [ProperSpace E] {P : Chapter06.BTRParams} {f : E → ℝ}
    {sufficient : ℕ → (E → ℝ) → E → E → Prop} (run : Chapter06.BTRRun f P sufficient)
    {F : Set E} (hF : IsClosed F) {z : E} {j : ℕ → ℕ} (hj : StrictMono j)
    (hz : Tendsto (run.x ∘ j) atTop (𝓝 z)) (hf : Continuous f)
    {ρ : ℝ} (hρ : 0 < ρ) (hmin : ∀ y ∈ F, 0 < dist y z → dist y z ≤ ρ → f z < f y)
    (hface : ∀ᶠ k in atTop, dist (run.x k) z ≤ ρ → run.x k ∈ F)
    (hsmall : ∀ ε > (0 : ℝ), ∃ R > (0 : ℝ), ∀ᶠ k in atTop, dist (run.x k) z < R →
      dist (run.x (k + 1)) (run.x k) ≤ ε) :
    Tendsto run.x atTop (𝓝 z) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let e := min (ε / 2) (ρ / 2)
  have he : 0 < e := lt_min (half_pos hε) (half_pos hρ)
  have heε : e ≤ ε / 2 := min_le_left _ _
  have heρ : e ≤ ρ / 2 := min_le_right _ _
  obtain ⟨R, hR, hstep⟩ := hsmall e he
  let r := min e R
  have hr : 0 < r := lt_min he hR
  have hre : r ≤ e := min_le_left _ _
  have hrR : r ≤ R := min_le_right _ _
  let A := (Metric.closedBall z (2 * e) ∩ F) ∩ {y : E | r ≤ dist y z}
  have hA : IsCompact A := ((isCompact_closedBall _ _).inter_right hF).inter_right
    (isClosed_le continuous_const (continuous_id.dist continuous_const))
  have hgap : ∃ b > f z, ∀ y ∈ A, b ≤ f y := by
    by_cases hne : A.Nonempty
    · obtain ⟨u, hu, hmu⟩ := hA.exists_isMinOn hne hf.continuousOn
      have hu₀ : r ≤ dist u z := hu.2
      have huρ : dist u z ≤ ρ := (show dist u z ≤ 2 * e from hu.1.1).trans (by linarith)
      exact ⟨f u, hmin u hu.1.2 (hr.trans_le hu₀) huρ, fun y hy ↦ (isMinOn_iff.mp hmu) y hy⟩
    · exact ⟨f z + 1, by linarith, fun y hy ↦ (hne ⟨y, hy⟩).elim⟩
  obtain ⟨b, hb, hgap⟩ := hgap
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hface.and hstep)
  obtain ⟨i, hi, hiz, hif⟩ := ((hj.tendsto_atTop.eventually_ge_atTop N).and
    ((hz.eventually (Metric.ball_mem_nhds z hr)).and
      ((hf.continuousAt.tendsto.comp hz).eventually_lt_const hb))).exists
  let n := j i
  have hnear (p : ℕ) : dist (run.x (n + p)) z < r := by
    induction p with
    | zero => exact hiz
    | succ p ih =>
      let k := n + p
      have hkN := hi.trans (Nat.le_add_right n p)
      have hmove := (hN k hkN).2 (ih.trans_le hrR)
      have hd : dist (run.x (k + 1)) z ≤ 2 * e := by
        have ht := dist_triangle (run.x (k + 1)) (run.x k) z
        linarith only [ht, hmove, ih, hre]
      have hpρ : dist (run.x (k + 1)) z ≤ ρ := hd.trans (by linarith)
      have hfnext : f (run.x (k + 1)) < b :=
        (run.objective_antitone (show n ≤ k + 1 by omega)).trans_lt hif
      rw [Nat.add_succ]
      exact lt_of_not_ge fun hh ↦ hfnext.not_ge
        (hgap _ ⟨⟨hd, (hN _ (hkN.trans (Nat.le_succ k))).1 hpρ⟩, hh⟩)
  exact eventually_atTop.mpr ⟨n, fun k hk ↦ by
    have hh := hnear (k - n)
    rw [Nat.add_sub_of_le hk] at hh
    exact hh.trans_le (hre.trans (heε.trans (half_le_self hε.le)))⟩

/-- **Theorem 12.4.3** of [conn2000trust], with the step bound of Lemma 12.4.2. Let $E$ be a real
inner product space in which closed balls are compact, and consider a run of the basic
trust-region algorithm for a continuous objective $f$. Let $F$ be closed, let a subsequence
$x_{j(k)}$ converge to $z$, let $\rho > 0$ and $\varepsilon > 0$, let $f(z) < f(y)$ for every
$y \in F$ with $0 < \operatorname{dist}(y, z) \le \rho$, and let
$\operatorname{dist}(x_k, z) \le \rho$ imply $x_k \in F$ for all large $k$. Let $y_k$ be
multipliers and $L_k$ the Lagrangian model (12.4.3) of $m_k$ with $y_k$. Suppose that, for all
large successful $k$ with $\operatorname{dist}(x_k, z) < \rho$,

* $\mathcal{A}(x_k + s_k) = \mathcal{A}(x_k)$ and $(y_k)_i = 0$ for $i \notin \mathcal{A}(x_k)$;
* $L_k$ is twice continuously differentiable and $DL_k(x_k)\, s_k = -\langle P_{T(x_k)}[-\nabla
  f(x_k)], s_k \rangle$;
* $\varepsilon \|s_k\|^2 \le \nabla^2 L_k(x_k + t s_k)[s_k, s_k]$ for every $t \in (0, 1]$.

Suppose also that for every $a > 0$ there is $R > 0$ such that, eventually,
$\operatorname{dist}(x_k, z) < R$ implies $\|P_{T(x_k)}[-\nabla f(x_k)]\| \le a$. Then
$x_k \to z$.

The step bound of Lemma 12.4.2 turns the small projected gradient into small steps, and
`ConnGouldToint.Chapter12.theorem_12_4_3` then applies.

**Reading.** Whole-sequence convergence assumes late nearby iterates lie on the identified closed
face and accepted steps become small near the limit. A companion gets the small-step condition from
explicit Lagrangian curvature and tangent-gradient control.
-/
theorem theorem_12_4_3_of_lagrangian [ProperSpace E] {P : Chapter06.BTRParams} {f : E → ℝ}
    {sufficient : ℕ → (E → ℝ) → E → E → Prop} (run : Chapter06.BTRRun f P sufficient)
    {C F : Set E} (hF : IsClosed F) {z : E} {j : ℕ → ℕ} (hj : StrictMono j)
    (hz : Tendsto (run.x ∘ j) atTop (𝓝 z)) (hf : Continuous f)
    {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (hmin : ∀ y ∈ F, 0 < dist y z → dist y z ≤ ρ → f z < f y)
    (hface : ∀ᶠ k in atTop, dist (run.x k) z ≤ ρ → run.x k ∈ F)
    {c : ι → E → ℝ} (y : ℕ → ι → ℝ)
    (hmodel : ∀ᶠ k in atTop, dist (run.x k) z < ρ → k ∈ run.successful →
      activeConstraintSet c (run.x k + run.s k) = activeConstraintSet c (run.x k) ∧
      (∀ i ∉ activeConstraintSet c (run.x k), y k i = 0) ∧
      ContDiff ℝ 2 (faceLagrangianModel (run.model k) c (y k)) ∧
      fderiv ℝ (faceLagrangianModel (run.model k) c (y k)) (run.x k) (run.s k) =
        -⟪bestApprox (tangentDirections C (run.x k)) (-gradient f (run.x k)), run.s k⟫ ∧
      ∀ t ∈ Ioc (0 : ℝ) 1, ε * ‖run.s k‖ ^ 2 ≤
        fderiv ℝ (fderiv ℝ (faceLagrangianModel (run.model k) c (y k)))
          (run.x k + t • run.s k) (run.s k) (run.s k))
    (hproj : ∀ a > (0 : ℝ), ∃ R > (0 : ℝ), ∀ᶠ k in atTop, dist (run.x k) z < R →
      ‖bestApprox (tangentDirections C (run.x k)) (-gradient f (run.x k))‖ ≤ a) :
    Tendsto run.x atTop (𝓝 z) := by
  apply theorem_12_4_3 run hF hj hz hf hρ hmin hface
  intro a ha
  obtain ⟨R, hR, hp⟩ := hproj (ε * a / 2) (by positivity)
  refine ⟨min R ρ, lt_min hR hρ, ?_⟩
  filter_upwards [hp, hmodel] with k hk hmk hnear
  by_cases hs : k ∈ run.successful
  · obtain ⟨hA, hy, hL, hg, hH⟩ := hmk (hnear.trans_le (min_le_right _ _)) hs
    have hprod := (lemma_12_4_2 hA hy hL hg hε (sub_nonneg.mp (run.predicted_pos k).le) hH).1
    have hinner := real_inner_le_norm
      (bestApprox (tangentDirections C (run.x k)) (-gradient f (run.x k))) (run.s k)
    have hupper := mul_le_mul_of_nonneg_right (hk (hnear.trans_le (min_le_left _ _)))
      (norm_nonneg (run.s k))
    rw [run.iterate_update, acceptStep_of_le hs, dist_eq_norm, add_sub_cancel_left]
    by_contra! hbig
    have hh := mul_pos (mul_pos hε (ha.trans hbig))
      (sub_pos.mpr hbig)
    nlinarith only [hprod, hinner, hupper, hh]
  · rw [run.iterate_eq_of_unsuccessful hs, dist_self]
    exact ha.le

omit [Fintype ι] [CompleteSpace E] in
/-- A step direction that keeps the active set extends feasibly through linear active constraints.
Let $a \ge 0$, $L$ and $\sigma$ satisfy $L a \le \sigma$, let $s \neq 0$ with
$\mathcal{A}(x + s) = \mathcal{A}(x)$, and suppose that

* each active $c_i$ is affine on the line through $x$ in the direction $s$: $c_i(x + ts) =
  c_i(x) + t\,(c_i(x + s) - c_i(x))$ for all $t \in \mathbb{R}$ and $i \in \mathcal{A}(x)$;
* each inactive constraint has slack $c_i(x) \ge \sigma$;
* each inactive $c_i$ satisfies $|c_i(z) - c_i(x)| \le L \|z - x\|$ for $\|z - x\| \le a$.

Then $x + (a / \|s\|)\, s$ satisfies $c_i \ge 0$ for every $i$. This gives the uniform feasible
extension that Lemma 12.4.4 of [conn2000trust] uses.

**Reading.** The model decrease result takes a uniform feasible extension in the step direction as a
hypothesis. The separate sufficient condition uses affine behavior of the active constraints along
the step and uniform slack and Lipschitz bounds for inactive constraints.
-/
theorem extendStep_mem_of_linear_active_face {c : ι → E → ℝ} {x s : E}
    {a L σ : ℝ} (ha : 0 ≤ a) (hσ : L * a ≤ σ) (hs : s ≠ 0)
    (hA : activeConstraintSet c (x + s) = activeConstraintSet c x)
    (haff : ∀ i ∈ activeConstraintSet c x, ∀ t : ℝ,
      c i (x + t • s) = c i x + t * (c i (x + s) - c i x))
    (hslack : ∀ i ∉ activeConstraintSet c x, σ ≤ c i x)
    (hlip : ∀ i ∉ activeConstraintSet c x, ∀ z, ‖z - x‖ ≤ a →
      |c i z - c i x| ≤ L * ‖z - x‖) :
    x + (a / ‖s‖) • s ∈ {z | ∀ i, 0 ≤ c i z} := by
  intro i
  by_cases hi : i ∈ activeConstraintSet c x
  · have hx : c i x = 0 := hi
    have hz : c i (x + s) = 0 := show i ∈ activeConstraintSet c (x + s) by rwa [hA]
    rw [haff i hi, hx, hz, sub_self, mul_zero, add_zero]
  · let z := x + (a / ‖s‖) • s
    have hz : ‖z - x‖ = a := by
      dsimp [z]
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (div_nonneg ha (norm_nonneg _)),
        div_mul_cancel₀ _ (norm_pos_iff.mpr hs).ne']
    have h := neg_abs_le (c i z - c i x)
    have hc := hlip i hi z hz.le
    rw [hz] at hc
    change 0 ≤ c i z
    linarith only [h, hc, hσ, hslack i hi]

/-- **Lemma 12.4.4** of [conn2000trust], with explicit face geometry. Let $E$ be a real Hilbert
space, let $\varepsilon, a, M, \beta, \kappa > 0$ with $a \le 1$, and let $\|s\| \le \Delta$ and
$\|s\| \le M$. Suppose that $x + (a / \|s\|)\, s \in C$ if $s \neq 0$, that
$$\varepsilon \|s\|^2 \le 2 \langle -\nabla f(x), s \rangle,$$
and that the model decrease condition AA.1b holds:
$$\kappa\, \pi(x) \min\{\pi(x)/\beta, \Delta\} \le m(x) - m(x + s),$$
where $\pi$ is the capped criticality measure (12.2.15). Then there is $\delta > 0$ with
$\delta \|s\|^2 \le m(x) - m(x + s)$.

**Reading.** The extension of the step direction by the uniform feasible length $a$ is an
explicit hypothesis; `ConnGouldToint.Chapter12.extendStep_mem_of_linear_active_face` supplies it
on a linear active face.

The proof takes $\delta = \kappa b \min\{b / \beta, 1\}$ with $b = \min\{1/M, a\varepsilon/2\}$,
which depends only on $\varepsilon$, $a$, $M$, $\beta$ and $\kappa$. The statement records only
the existence of $\delta$ for the given step. The linear term is the full one,
$\langle -\nabla f(x), s \rangle$; on a linear active face it equals the tangent linear term of
Lemma 12.4.2.

**Reading.** The model decrease result takes a uniform feasible extension in the step direction as a
hypothesis. The separate sufficient condition uses affine behavior of the active constraints along
the step and uniform slack and Lipschitz bounds for inactive constraints.
-/
theorem lemma_12_4_4 {C : Set E} {m f : E → ℝ} {x s : E}
    {ε a M Δ β κ : ℝ} (hε : 0 < ε) (ha : 0 < a) (ha₁ : a ≤ 1)
    (hM : 0 < M) (hβ : 0 < β) (hκ : 0 < κ)
    (hstep : ‖s‖ ≤ Δ) (hbound : ‖s‖ ≤ M)
    (hextend : s ≠ 0 → x + (a / ‖s‖) • s ∈ C)
    (hlin : ε * ‖s‖ ^ 2 ≤ 2 * ⟪-gradient f x, s⟫)
    (hdec : κ * cappedCriticality C f x * min (cappedCriticality C f x / β) Δ ≤
      m x - m (x + s)) :
    ∃ δ > 0, δ * ‖s‖ ^ 2 ≤ m x - m (x + s) := by
  let b := min (1 / M) (a * ε / 2)
  have hb : 0 < b := lt_min (one_div_pos.mpr hM) (by positivity)
  refine ⟨κ * b * min (b / β) 1, mul_pos (mul_pos hκ hb) (lt_min (div_pos hb hβ) zero_lt_one), ?_⟩
  by_cases hs : s = 0
  · simp [hs]
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs
  have hscaled : ‖(a / ‖s‖) • s‖ ≤ (1 : ℝ) := by
    rw [norm_smul, Real.norm_of_nonneg (div_nonneg ha.le hsn.le), div_mul_cancel₀ _ hsn.ne']
    exact ha₁
  have hχ := inner_le_linearDecrease (v := -gradient f x) (hextend hs) hscaled
  have hscale : (a * ε / 2) * ‖s‖ ≤ ⟪-gradient f x, (a / ‖s‖) • s⟫ := by
    rw [real_inner_smul_right]
    calc
      _ ≤ (a * ⟪-gradient f x, s⟫) / ‖s‖ := by
        apply (le_div_iff₀ hsn).mpr
        nlinarith only [mul_le_mul_of_nonneg_left hlin ha.le]
      _ = _ := by ring
  have hbχ : b * ‖s‖ ≤ cappedCriticality C f x := by
    apply le_min
    · exact ((mul_le_mul_of_nonneg_right (min_le_left _ _) hsn.le).trans
        (mul_le_mul_of_nonneg_left hbound (one_div_nonneg.mpr hM.le))).trans_eq
          (one_div_mul_cancel hM.ne')
    · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) hsn.le).trans (hscale.trans hχ)
  have hmin : min (b / β) 1 * ‖s‖ ≤ min (cappedCriticality C f x / β) Δ := by
    rw [min_mul_of_nonneg _ _ hsn.le, one_mul]
    refine min_le_min ?_ hstep
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hbχ hβ.le
  have hbmin : 0 ≤ min (b / β) 1 * ‖s‖ := by positivity
  have hpred := mul_le_mul (mul_le_mul_of_nonneg_left hbχ hκ.le) hmin hbmin
    (mul_nonneg hκ.le ((mul_nonneg hb.le hsn.le).trans hbχ))
  exact (le_trans (by nlinarith only [hpred]) hdec)

omit [Fintype ι] [CompleteSpace E] in
/-- **Theorem 12.4.5** of [conn2000trust]. Consider a run of the basic trust-region algorithm for a
twice continuously differentiable objective $f$. Suppose that each model $m_k$ and its
derivative are differentiable on the segment $[x_k, x_k + s_k]$, that $m_k(x_k) = f(x_k)$ and
$Df(x_k) = Dm_k(x_k)$ for all $k$, and that for every $a > 0$, eventually,
$$\|\nabla^2 f(z) - \nabla^2 m_k(z)\| \le a \quad \text{for all } z \in [x_k, x_k + s_k].$$
Let $\delta > 0$ with $\delta \|s_k\|^2 \le m_k(x_k) - m_k(x_k + s_k)$ for all large $k$. Then
every sufficiently late iteration is very successful, and there is $r > 0$ with $\Delta_k \ge r$
for all $k$.

**Reading.** The Hessian agreement on the trial segments, the estimate (12.4.7) for linear
active constraints, is assumed directly. The quadratic decrease is the conclusion of Lemma
12.4.4.

**Reading.** The theorem directly assumes asymptotic Hessian agreement on the full trial segments
and a quadratic lower bound on predicted decrease, alongside equality of values and gradients at the
base.
-/
theorem theorem_12_4_5 {P : Chapter06.BTRParams} {f : E → ℝ}
    {sufficient : ℕ → (E → ℝ) → E → E → Prop} (run : Chapter06.BTRRun f P sufficient)
    (hf : ContDiff ℝ 2 f)
    (hm : ∀ k z, z ∈ segment ℝ (run.x k) (run.x k + run.s k) →
      DifferentiableAt ℝ (run.model k) z)
    (hDm : ∀ k z, z ∈ segment ℝ (run.x k) (run.x k + run.s k) →
      DifferentiableAt ℝ (fderiv ℝ (run.model k)) z)
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (hgrad : ∀ k, fderiv ℝ f (run.x k) = fderiv ℝ (run.model k) (run.x k))
    (hagree : ∀ a > (0 : ℝ), ∀ᶠ k in atTop, ∀ z ∈ segment ℝ (run.x k) (run.x k + run.s k),
      ‖fderiv ℝ (fderiv ℝ f) z - fderiv ℝ (fderiv ℝ (run.model k)) z‖ ≤ a)
    {δ : ℝ} (hδ : 0 < δ) (hdec : ∀ᶠ k in atTop, δ * ‖run.s k‖ ^ 2 ≤
      run.model k (run.x k) - run.model k (run.x k + run.s k)) :
    (∀ᶠ k in atTop, k ∈ run.verySuccessful) ∧ ∃ r > 0, ∀ k, r ≤ run.Δ k := by
  let a := 2 * (1 - P.η₂) * δ
  have hη : 0 < 1 - P.η₂ := sub_pos.mpr P.eta₂_lt_one
  have ha : 0 < a := by dsimp [a]; positivity
  have hv : ∀ᶠ k in atTop, k ∈ run.verySuccessful := by
    filter_upwards [hagree a ha, hdec] with k hh hd
    have herr := Chapter06.abs_model_error_le hf (hval k) (hgrad k) (hm k) (hDm k) hh
    have he : |f (run.x k + run.s k) -
        (f (run.x k) - (run.model k (run.x k) - run.model k (run.x k + run.s k)))| ≤
        (1 - P.η₂) * (run.model k (run.x k) - run.model k (run.x k + run.s k)) := by
      rw [hval k, sub_sub_cancel]
      refine herr.trans ?_
      dsimp [a]
      have hh' := mul_le_mul_of_nonneg_left hd hη.le
      linarith only [hh', show (1 / 2 : ℝ) * (2 * (1 - P.η₂) * δ) * ‖run.s k‖ ^ 2 =
        (1 - P.η₂) * (δ * ‖run.s k‖ ^ 2) by ring]
    simpa only [sub_sub_cancel, Chapter06.BTRRun.verySuccessful, Set.mem_ofPred_eq,
      Chapter06.btrRatio] using le_reductionRatio_of_abs_sub_le (run.predicted_pos k) he
  exact ⟨hv, run.exists_delta_lower_bound_of_eventually_verySuccessful hv⟩

section FaceBoundary

open scoped ENNReal

/-- The **active equality locus** at $x$: the set of points $z$ at which every constraint active at
$x$ vanishes, $\{z : c_i(z) = 0 \text{ for all } i \in \mathcal{A}(x)\}$.

**Reading.** The frontier is taken inside the active equality locus. The extended distance is
infinite for empty frontier; continuity and feasibility give strictly positive distance.
-/
def activeEqualityLocus (c : ι → E → ℝ) (x : E) : Set E :=
  {z | ∀ i ∈ activeConstraintSet c x, c i z = 0}

/-- **Equation (12.4.16)** of [conn2000trust]. Let $\mathcal{L}$ be the active equality locus at
$x$, with the subspace topology. The **face clearance** of $x$ is the extended distance in
$\mathcal{L}$ from $x$ to the frontier, relative to $\mathcal{L}$, of $C \cap \mathcal{L}$.

**Reading.** The distance uses the frontier relative to the active equality locus. When that
frontier is empty, the distance is $+\infty$.

The value lies in $[0, \infty]$ and is `Metric.infEDist` in the subtype
`ConnGouldToint.Chapter12.activeEqualityLocus c x`.

**Reading.** The frontier is taken inside the active equality locus. The extended distance is
infinite for empty frontier; continuity and feasibility give strictly positive distance.
-/
noncomputable def activeFaceBoundaryDistance (C : Set E) (c : ι → E → ℝ) (x : E) :
    ℝ≥0∞ :=
  Metric.infEDist (⟨x, fun _ hi ↦ hi⟩ : activeEqualityLocus c x)
    (frontier ((↑) ⁻¹' C : Set (activeEqualityLocus c x)))

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- **Equation (12.4.16)** of [conn2000trust], positivity. Let
$C = \{z : c_i(z) \ge 0 \text{ for all } i\}$ (AC.7), with continuous $c_i$, and let $x \in C$.
Then the face clearance of $x$ is positive.

Every inactive inequality has strict slack at $x$, so $x$ is interior to $C \cap \mathcal{L}$
relative to the active equality locus $\mathcal{L}$.

**Reading.** The frontier is taken inside the active equality locus. The extended distance is
infinite for empty frontier; continuity and feasibility give strictly positive distance.
-/
theorem activeFaceBoundaryDistance_pos {C : Set E} {c : ι → E → ℝ} {x : E}
    (hC : Chapter03.AC7 C c) (hc : ∀ i, Continuous (c i)) (hx : x ∈ C) :
    0 < activeFaceBoundaryDistance C c x := by
  classical
  let L := activeEqualityLocus c x
  let z : L := ⟨x, fun _ hi ↦ hi⟩
  let F : Set L := (↑) ⁻¹' C
  let U : Set L := ⋂ i : {i // i ∉ activeConstraintSet c x}, {y | 0 < c i y}
  have hU : IsOpen U := isOpen_iInter_of_finite fun i ↦
    isOpen_lt continuous_const ((hc i).comp continuous_subtype_val)
  have hzx : z ∈ U := by
    apply mem_iInter.mpr
    intro i
    have hge : 0 ≤ c i x := by
      have hx' := hx
      rw [hC] at hx'
      exact hx' i
    exact lt_of_le_of_ne hge (Ne.symm i.property)
  have hUF : U ⊆ F := by
    intro y hy
    change (y : E) ∈ C
    rw [hC]
    intro i
    by_cases hi : i ∈ activeConstraintSet c x
    · exact (y.property i hi).ge
    · exact (mem_iInter.mp hy ⟨i, hi⟩ : 0 < c i y).le
  have hzF : z ∈ interior F :=
    mem_interior_iff_mem_nhds.mpr (mem_of_superset (hU.mem_nhds hzx) hUF)
  change 0 < Metric.infEDist z (frontier F)
  rw [Metric.infEDist_pos_iff_notMem_closure, isClosed_frontier.closure_eq]
  exact fun h ↦ h.2 hzF

end FaceBoundary

omit [Fintype ι] [CompleteSpace E] in
/-- **Equation (12.4.14)** of [conn2000trust], corrected. Let $C, F \subseteq E$, let $m$ be a
model, $x$ a base point, $u$ a direction, $q$, $b$ and $\tau$ real numbers and
$j \in \mathbb{N}$. Put $t_j = q^j$. The $j$-th **projected eigenpoint trial is accepted** if
$P_C[x + t_j u] \in F$ and
$$m(P_C[x + t_j u]) \le m(x) + b\, \tau\, (t_j \|u\|)^2.$$

**Correction.** The printed test has $-b\, \tau$ in place of $b\, \tau$. For a negative
eigenvalue estimate $\tau < 0$ it accepts a strict model increase; see
`ConnGouldToint.Chapter12.eigenTrial_printed_sign_counterexample`. With the sign here,
$\tau < 0$ requires a decrease. The membership $P_C[x + t_j u] \in F$ adds the active-face test
to the backtracking.

The projection $P_C[x + t u]$ is `Optimization.projectedRay C x u t`, and $t_j$ is
`ConnGouldToint.Chapter06.eigenTrialTime q j`.

**Correction.** For negative curvature the test adds a negative term to the current model value,
proportional to the squared scaled trial length. The printed subtraction accepts strict model
increase in a smooth one-dimensional example.
-/
def ProjectedEigenTrialAccepted (C F : Set E) (m : E → ℝ) (x u : E)
    (q b τ : ℝ) (j : ℕ) : Prop :=
  projectedRay C x u (Chapter06.eigenTrialTime q j) ∈ F ∧
  m (projectedRay C x u (Chapter06.eigenTrialTime q j)) ≤
    m x + b * τ * (Chapter06.eigenTrialTime q j * ‖u‖) ^ 2

private theorem sq_min_eq_min_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (min a b) ^ 2 = min (a ^ 2) (b ^ 2) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (pow_le_pow_left₀ ha h 2)]
  · rw [min_eq_right h, min_eq_right (pow_le_pow_left₀ hb h 2)]

/-- **Equations (12.4.19)–(12.4.22)** of [conn2000trust]. Let $C$ be closed and convex, let
$x \in C$, $t \ge 0$, and put $p = P_C[x + tu]$. Suppose that $\mathcal{A}(p) = \mathcal{A}(x)$,
that $y_i = 0$ for $i \notin \mathcal{A}(x)$, and that $\|p - (x + tu)\| \le B (t\|u\|)^2$. Let
$S$ be an open set that contains the segment $[x, p]$, on which the Lagrangian model $L$ of
(12.4.3) is twice continuously differentiable with $\|\nabla^2 L(z) - \nabla^2 L(x)\| \le \gamma
\|z - x\|$ for $z \in S$, where $\gamma \ge 0$. If
$\nabla^2 L(x)[u, u] \le \kappa \tau \|u\|^2$, then, with $H = \nabla^2 L(x)$,
$$m(p) \le m(x) + t\, DL(x)\, u + \Bigl(\tfrac{\kappa}{2} \tau + \|DL(x)\|\, B\Bigr)(t\|u\|)^2 +
  \Bigl(\tfrac{\gamma}{6} + \|H\|\, B\Bigr)(t\|u\|)^3.$$

The change in the quadratic term is cubic, because the trial step $tu$ and the projected step
$p - x$ both have length at most the ray length $t\|u\|$.

**Correction.** The Taylor estimate takes the projected-ray correction and local Hessian bounds
explicitly. The first acceptable trial gives a positive decrease proportional to minus the negative
eigenvalue and the minimum of the squared scales, including face radius. The printed bound uses the
negative eigenvalue itself.
-/
theorem projectedRay_taylor_upper_of_face {C : Set E} {m : E → ℝ}
    {c : ι → E → ℝ} {y : ι → ℝ} {x u : E} {t B γ κ τ : ℝ} (ht : 0 ≤ t)
    (hA : activeConstraintSet c (projectedRay C x u t) = activeConstraintSet c x)
    (hy : ∀ i ∉ activeConstraintSet c x, y i = 0)
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hx : x ∈ C)
    (hproj : ‖projectedRay C x u t - (x + t • u)‖ ≤ B * (t * ‖u‖) ^ 2)
    {S : Set E} (hS : IsOpen S) (hL : ContDiffOn ℝ 2 (faceLagrangianModel m c y) S)
    (hseg : ∀ a ∈ Icc (0 : ℝ) 1, x + a • (projectedRay C x u t - x) ∈ S)
    (hlip : ∀ z ∈ S, ‖fderiv ℝ (fderiv ℝ (faceLagrangianModel m c y)) z -
      fderiv ℝ (fderiv ℝ (faceLagrangianModel m c y)) x‖ ≤ γ * ‖z - x‖)
    (hγ : 0 ≤ γ)
    (hcurv : fderiv ℝ (fderiv ℝ (faceLagrangianModel m c y)) x u u ≤ κ * τ * ‖u‖ ^ 2) :
    let L := faceLagrangianModel m c y
    let H := fderiv ℝ (fderiv ℝ L) x
    m (projectedRay C x u t) ≤ m x + t * fderiv ℝ L x u +
      (κ / 2 * τ + ‖fderiv ℝ L x‖ * B) * (t * ‖u‖) ^ 2 +
      (γ / 6 + ‖H‖ * B) * (t * ‖u‖) ^ 3 := by
  let L := faceLagrangianModel m c y
  let H := fderiv ℝ (fderiv ℝ L) x
  let z := projectedRay C x u t
  let v := z - x
  let w := t • u
  let a := t * ‖u‖
  have hself : bestApprox C x = x :=
    (bestApprox_eq_iff ⟨x, hx⟩ hclosed hconv).mpr ⟨hx, by simp⟩
  have hstep : ‖v‖ ≤ a := by
    have h := norm_bestApprox_sub_bestApprox_le ⟨x, hx⟩ hclosed hconv (x + t • u) x
    rw [hself, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht] at h
    exact h
  have hw : ‖w‖ = a := by simp [w, a, norm_smul, Real.norm_of_nonneg ht]
  have hvw : ‖v - w‖ ≤ B * a ^ 2 := by
    simpa only [v, w, z, sub_sub] using hproj
  have hB : 0 ≤ B * a ^ 2 := (norm_nonneg _).trans hvw
  have hnorm (p q : E) : |H p q| ≤ ‖H‖ * ‖p‖ * ‖q‖ := by
    rw [← Real.norm_eq_abs]
    exact ((H p).le_opNorm q).trans (mul_le_mul_of_nonneg_right (H.le_opNorm p) (norm_nonneg q))
  have hquad : H v v - H w w ≤ 2 * ‖H‖ * B * a ^ 3 := by
    have heq : H v v - H w w = H (v - w) v + H w (v - w) := by
      simp only [map_sub, sub_apply]
      ring
    rw [heq]
    have hb₁ := (le_abs_self _).trans ((hnorm (v - w) v).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left hvw (norm_nonneg H)) hstep (norm_nonneg v)
        (mul_nonneg (norm_nonneg H) hB)))
    have hb₂ := (le_abs_self _).trans ((hnorm w (v - w)).trans
      (mul_le_mul_of_nonneg_left hvw (mul_nonneg (norm_nonneg H) (norm_nonneg w))))
    rw [hw] at hb₂
    nlinarith only [hb₁, hb₂]
  have hlinear : fderiv ℝ L x v - t * fderiv ℝ L x u ≤ ‖fderiv ℝ L x‖ * B * a ^ 2 := by
    calc
      _ = fderiv ℝ L x (v - w) := by simp only [map_sub, w, map_smul, smul_eq_mul]
      _ ≤ ‖fderiv ℝ L x (v - w)‖ := by rw [Real.norm_eq_abs]; exact le_abs_self _
      _ ≤ ‖fderiv ℝ L x‖ * ‖v - w‖ := (fderiv ℝ L x).le_opNorm _
      _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hvw (norm_nonneg _)
  have hq : H w w ≤ κ * τ * a ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hcurv (sq_nonneg t)
    dsimp [H, w, a] at *
    simp only [map_smul, smul_apply, smul_eq_mul]
    nlinarith only [h]
  have hTaylor := (le_of_abs_le
    (abs_sub_secondOrder_le_of_lipschitzAt_segment hS hL hseg hlip)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hstep 3) (by positivity))
  have hz : x + v = z := by dsimp [v]; abel
  change L (x + v) - (L x + fderiv ℝ L x v + (1 / 2 : ℝ) * H v v) ≤ _ at hTaylor
  rw [hz, show L z = m z from faceLagrangianModel_eq_of_active hA hy,
    show L x = m x from faceLagrangianModel_eq_of_active rfl hy] at hTaylor
  change m z ≤ m x + t * fderiv ℝ L x u + (κ / 2 * τ + ‖fderiv ℝ L x‖ * B) * a ^ 2 +
    (γ / 6 + ‖H‖ * B) * a ^ 3
  nlinarith only [hTaylor, hlinear, hquad, hq]

omit [Fintype ι] [CompleteSpace E] in
/-- **Theorem 12.4.6** of [conn2000trust], corrected. Let $0 < q < 1$, $b > 0$ and $\kappa$ with
$b < \kappa/2$, let $\tau < 0$, $u \neq 0$, $\sigma > 0$, $R > 0$, $g \le 0$ and
$D \le (\kappa/2 - b)(-\tau)/2$. Suppose that, for every $t \in (0, 1]$ with
$t\|u\| \le \sigma$, the point $P_C[x + tu]$ lies in $F$, and, if also $t\|u\| \le 1$,
$$m(P_C[x + tu]) \le m(x) + t g + \Bigl(\tfrac{\kappa}{2} \tau + D\Bigr)(t\|u\|)^2 +
  R\,(t\|u\|)^3.$$
Then there is a first index $j$ at which the projected eigenpoint trial (12.4.14) is accepted,
and with $t_j = q^j$,
$$b \Bigl(q \min\Bigl\{1, \frac{\kappa/2 - b}{2R}\Bigr\}\Bigr)^2 (-\tau) \min\{\|u\|^2, 1,
  \sigma^2, \tau^2\} \le m(x) - m(P_C[x + t_j u]).$$

**Correction.** The theorem uses the corrected sign of the acceptance test (12.4.14), and the
decrease bound includes the face radius $\sigma$. With the printed sign the test can accept a
model increase.

The Taylor hypothesis is the form that
`ConnGouldToint.Chapter12.projectedRay_taylor_upper_of_face` gives: $D$ collects the errors of
the tangent gradient and the multipliers, and $R$ the cubic remainder.

**Correction.** The Taylor estimate takes the projected-ray correction and local Hessian bounds
explicitly. The first acceptable trial gives a positive decrease proportional to minus the negative
eigenvalue and the minimum of the squared scales, including face radius. The printed bound uses the
negative eigenvalue itself.
-/
theorem theorem_12_4_6 {C F : Set E} {m : E → ℝ} {x u : E}
    {q b κ τ σ D R g : ℝ} (hq : 0 < q) (hq' : q < 1) (hb : 0 < b)
    (hbκ : b < κ / 2) (hτ : τ < 0) (hu : u ≠ 0) (hσ : 0 < σ) (hR : 0 < R)
    (hg : g ≤ 0) (hD : D ≤ (κ / 2 - b) * (-τ) / 2)
    (hface : ∀ t ∈ Ioc (0 : ℝ) 1, t * ‖u‖ ≤ σ → projectedRay C x u t ∈ F)
    (hTaylor : ∀ t ∈ Ioc (0 : ℝ) 1, t * ‖u‖ ≤ 1 → t * ‖u‖ ≤ σ →
      m (projectedRay C x u t) ≤
        m x + t * g + (κ / 2 * τ + D) * (t * ‖u‖) ^ 2 + R * (t * ‖u‖) ^ 3) :
    ∃ j, ProjectedEigenTrialAccepted C F m x u q b τ j ∧
      (∀ i < j, ¬ ProjectedEigenTrialAccepted C F m x u q b τ i) ∧
      b * (q * min 1 ((κ / 2 - b) / (2 * R))) ^ 2 * (-τ) *
        min (‖u‖ ^ 2) (min 1 (min (σ ^ 2) (τ ^ 2))) ≤
          m x - m (projectedRay C x u (Chapter06.eigenTrialTime q j)) := by
  let U := ‖u‖
  let d := (κ / 2 - b) / (2 * R)
  have hU : 0 < U := norm_pos_iff.mpr hu
  have hτ' : 0 < -τ := neg_pos.mpr hτ
  have hd : 0 < d := div_pos (sub_pos.mpr hbκ) (by positivity)
  let a := min 1 (min σ (d * (-τ)))
  have ha : 0 < a := lt_min zero_lt_one (lt_min hσ (mul_pos hd hτ'))
  have haccept (j : ℕ) (hj : Chapter06.eigenTrialTime q j * U ≤ a) :
      ProjectedEigenTrialAccepted C F m x u q b τ j := by
    let t := Chapter06.eigenTrialTime q j
    have ht : t ∈ Ioc (0 : ℝ) 1 := ⟨pow_pos hq j, pow_le_one₀ hq.le hq'.le⟩
    have ht₁ : t * U ≤ 1 := hj.trans (min_le_left _ _)
    have htσ : t * U ≤ σ := hj.trans ((min_le_right _ _).trans (min_le_left _ _))
    have htD : R * (t * U) ≤ (κ / 2 - b) * (-τ) / 2 := by
      have hh : t * U ≤ d * (-τ) := hj.trans ((min_le_right _ _).trans (min_le_right _ _))
      have hh' := mul_le_mul_of_nonneg_left hh hR.le
      have he : R * (d * (-τ)) = (κ / 2 - b) * (-τ) / 2 := by
        dsimp [d]
        field_simp
      exact hh'.trans_eq he
    refine ⟨hface t ht htσ, (hTaylor t ht ht₁ htσ).trans ?_⟩
    have hlin := mul_nonpos_of_nonneg_of_nonpos ht.1.le hg
    have hquad := mul_le_mul_of_nonneg_right hD (sq_nonneg (t * U))
    have hcubic := mul_le_mul_of_nonneg_right htD (sq_nonneg (t * U))
    change m x + t * g + (κ / 2 * τ + D) * (t * U) ^ 2 + R * (t * U) ^ 3 ≤
      m x + b * τ * (t * U) ^ 2
    nlinarith only [hlin, hquad, hcubic]
  obtain ⟨j, hj, hfirst, hlength⟩ :=
    Chapter06.exists_first_eigenTrial_of_small_length hq hq' ha haccept
  refine ⟨j, hj, hfirst, ?_⟩
  let w := min 1 d
  let v := min U (min 1 (min σ (-τ)))
  have hw : 0 < w := lt_min zero_lt_one hd
  have hv : 0 < v := lt_min hU (lt_min zero_lt_one (lt_min hσ hτ'))
  have hva : w * v ≤ a := by
    have hbound := mul_le_of_le_one_left hv.le (show w ≤ 1 from min_le_left _ _)
    refine le_min (hbound.trans ((min_le_right _ _).trans (min_le_left _ _))) (le_min ?_ ?_)
    · exact hbound.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    · exact mul_le_mul (show w ≤ d from min_le_right _ _)
        ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))) hv.le hd.le
  have hqv : q * w * v ≤ min U (q * a) := by
    refine le_min ?_ ?_
    · have hqw : q * w ≤ 1 :=
        (mul_le_of_le_one_right hq.le (min_le_left _ _)).trans hq'.le
      exact (mul_le_of_le_one_left hv.le hqw).trans (min_le_left _ _)
    · rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hva hq.le
  have hsquare := pow_le_pow_left₀ (mul_nonneg (mul_nonneg hq.le hw.le) hv.le)
    (hqv.trans hlength) 2
  have hv2 : v ^ 2 = min (U ^ 2) (min 1 (min (σ ^ 2) (τ ^ 2))) := by
    dsimp [v]
    rw [sq_min_eq_min_sq hU.le (le_min zero_le_one (le_min hσ.le hτ'.le)),
      sq_min_eq_min_sq zero_le_one (le_min hσ.le hτ'.le), sq_min_eq_min_sq hσ.le hτ'.le]
    simp
  rw [mul_pow, hv2] at hsquare
  have hp := mul_le_mul_of_nonneg_left hsquare (mul_nonneg hb.le hτ'.le)
  have hmodel := hj.2
  change m (projectedRay C x u (Chapter06.eigenTrialTime q j)) ≤
    m x + b * τ * (Chapter06.eigenTrialTime q j * U) ^ 2 at hmodel
  change b * (q * w) ^ 2 * (-τ) * min (U ^ 2) (min 1 (min (σ ^ 2) (τ ^ 2))) ≤ _
  linarith only [hp, hmodel]

/-- **Equation (12.4.14)** of [conn2000trust], counterexample to the printed sign. There is a twice
continuously differentiable $m : \mathbb{R} \to \mathbb{R}$ with $m'(0) = 0$ and $m''(0) = -1$
such that
$$m(1) \le m(0) - \tfrac14 \cdot (-1) \quad\text{and}\quad m(0) < m(1).$$
So the printed test with $b = 1/4$, $\tau = -1$, unit direction and initial trial time $1$
accepts a strict increase of the model.

The function is $m(t) = -t^2/2 + 3t^3/4$, with $m(1) = 1/4$.

**Correction.** For negative curvature the test adds a negative term to the current model value,
proportional to the squared scaled trial length. The printed subtraction accepts strict model
increase in a smooth one-dimensional example.
-/
theorem eigenTrial_printed_sign_counterexample :
    ∃ m : ℝ → ℝ, ContDiff ℝ 2 m ∧ deriv m 0 = 0 ∧ iteratedDeriv 2 m 0 = -1 ∧
      m 1 ≤ m 0 - (1 / 4 : ℝ) * (-1) ∧ m 0 < m 1 := by
  let m (t : ℝ) := -(1 / 2 : ℝ) * t ^ 2 + (3 / 4 : ℝ) * t ^ 3
  have hderiv (t : ℝ) : deriv m t = -t + (9 / 4 : ℝ) * t ^ 2 := by
    have h := ((((hasDerivAt_id t).fun_pow 2).const_mul (-(1 / 2 : ℝ))).fun_add
      (((hasDerivAt_id t).fun_pow 3).const_mul (3 / 4 : ℝ))).deriv
    exact h.trans (by dsimp; ring)
  have hm : ContDiff ℝ 2 m := (contDiff_const.mul (contDiff_id.pow 2)).add
    (contDiff_const.mul (contDiff_id.pow 3))
  refine ⟨m, hm, ?_, ?_, ?_, ?_⟩
  · norm_num [hderiv]
  · rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one, funext hderiv]
    have h := ((hasDerivAt_id (0 : ℝ)).fun_neg.fun_add
      (((hasDerivAt_id (0 : ℝ)).fun_pow 2).const_mul (9 / 4 : ℝ))).deriv
    simpa using h
  · norm_num [m]
  · norm_num [m]

end ConnGouldToint.Chapter12
