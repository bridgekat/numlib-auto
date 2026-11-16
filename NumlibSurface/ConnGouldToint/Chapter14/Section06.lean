/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter14.Section02
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Conn, Gould and Toint, Section 14.6: Smooth exact penalties

This module formalizes the smooth exact penalty function of [conn2000trust], Section 14.6, for the
problem of minimizing $f(x)$ subject to $c(x) = 0$. The penalty function combines the Lagrangian at
the least-squares multiplier $y(x) = y^{LS}(x)$ of (14.2.8) with a quadratic penalty term:
$$\phi(x, \sigma) = f(x) - \langle y(x), c(x) \rangle + \frac\sigma2 \|c(x)\|^2.$$
The module computes its gradient (14.6.3) and Hessian (14.6.4), with $A = c'(x)$ and $D = y'(x)$. At
a feasible point with $A$ surjective, the gradient is the gradient of the Lagrangian (14.6.6).
Theorem 14.6.1 shows that, for all large $\sigma$, the Hessian of $\phi$ is positive definite if and
only if the Hessian of the Lagrangian is positive definite on $\ker A$. The derivative of $y$ comes
from Lemma 14.2.1.

## Main definitions

* Equation (14.6.2), `ConnGouldToint.Chapter14.smoothExactPenalty`: the smooth exact penalty
  function.

## Main results

* Equation (14.6.3), `ConnGouldToint.Chapter14.gradient_smoothExactPenalty_eq`: the gradient of the
  penalty function.
* Equation (14.6.4), `ConnGouldToint.Chapter14.fderiv_gradient_smoothExactPenalty_eq`: the Hessian
  of the penalty function at a point where $A$ is surjective.
* Equation (14.6.4), `ConnGouldToint.Chapter14.fderiv_gradient_smoothExactPenalty_at_feasible`: the
  Hessian at a feasible point.
* Equation (14.6.4), `ConnGouldToint.Chapter14.smoothExactPenalty_printed_hessian_counterexample`:
  the printed Hessian formula fails at an infeasible point.
* Equation (14.6.6), `ConnGouldToint.Chapter14.fderiv_smoothExactPenalty_at_feasible`: the
  derivative at a feasible point.
* Theorem 14.6.1, `ConnGouldToint.Chapter14.theorem_14_6_1_quadratic_test`: the quadratic-form test
  behind Theorem 14.6.1.
* Theorem 14.6.1, `ConnGouldToint.Chapter14.theorem_14_6_1`: second-order equivalence at a feasible
  point for large $\sigma$.

## Deviations from the source

* **Equation (14.6.4)** (correction). Away from the feasible set, the Hessian contains the
  derivative of $z \mapsto y'(z)^* c(x)$, which the printed formula omits. A scalar cubic shows that
  this term can be nonzero. See `ConnGouldToint.Chapter14.fderiv_gradient_smoothExactPenalty_eq` and
  `ConnGouldToint.Chapter14.smoothExactPenalty_printed_hessian_counterexample`.
-/

open Filter Topology Asymptotics
open scoped RealInnerProductSpace Asymptotics

namespace ConnGouldToint.Chapter14

variable {G F : Type*}
variable [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- **Equation (14.6.2)** of [conn2000trust]. The **smooth exact penalty function** with parameter
$\sigma$ is
$$\phi(x, \sigma) = \ell\big(x, y(x)\big) + \frac\sigma2 \|c(x)\|^2 = f(x) - \langle y(x), c(x)
  \rangle + \frac\sigma2 \|c(x)\|^2,$$
where $y(x) = (c'(x) c'(x)^*)^{-1} c'(x) \nabla f(x)$ is the least-squares multiplier (14.2.8).

The multiplier is evaluated at the same point $x$ as the objective and the constraints. -/
noncomputable def smoothExactPenalty (f : G → ℝ) (c : G → F) (σ : ℝ) (x : G) : ℝ :=
  lagrangian f c (leastSquaresMultiplier (fderiv ℝ c x) (gradient f x)) x +
    σ / 2 * ‖c x‖ ^ 2

/-- **Equation (14.6.6)** of [conn2000trust]. Let $F$ be finite-dimensional, let $f$ and $c$ be
twice continuously differentiable, let $c(x) = 0$ and let $c'(x)$ be surjective. Then for every
$\sigma$
$$\phi'(x, \sigma) = \nabla_x \ell\big(x, y(x)\big),$$
the derivative of the Lagrangian with the multiplier $y(x)$ held fixed.

The derivative of the multiplier estimate and the derivative of the penalty term are both
multiplied by the residual $c(x) = 0$. -/
theorem fderiv_smoothExactPenalty_at_feasible [FiniteDimensional ℝ F]
    {f : G → ℝ} {c : G → F} (hf : ContDiff ℝ 2 f) (hc : ContDiff ℝ 2 c)
    {x : G} (hcx : c x = 0) (hA : Function.Surjective (fderiv ℝ c x)) (σ : ℝ) :
    fderiv ℝ (smoothExactPenalty f c σ) x =
      fderiv ℝ (lagrangian f c (leastSquaresMultiplier (fderiv ℝ c x) (gradient f x))) x := by
  let y := fun z ↦ leastSquaresMultiplier (fderiv ℝ c z) (gradient f z)
  have hy : DifferentiableAt ℝ y x :=
    (lemma_14_2_1 hf hc (multiplierGram_isUnit_of_surjective hA)).1
  have hf' := (hf.differentiable (by norm_num) x).hasFDerivAt
  have hc' := (hc.differentiable (by norm_num) x).hasFDerivAt
  have h₁ := hf'.sub (hy.hasFDerivAt.inner ℝ hc')
  have h₂ := hf'.sub ((hasFDerivAt_const (y x) x).inner ℝ hc')
  have h₃ := h₁.add (hc'.norm_sq.const_mul (σ / 2))
  change HasFDerivAt (lagrangian f c (y x)) _ _ at h₂
  change HasFDerivAt (smoothExactPenalty f c σ) _ _ at h₃
  rw [h₃.fderiv, h₂.fderiv]
  apply ContinuousLinearMap.ext
  intro v
  simp [hcx]

omit [CompleteSpace G] [CompleteSpace F] in
/-- **Theorem 14.6.1** of [conn2000trust], the quadratic test. Let $G$ be finite-dimensional, let
$A : G \to F$ and $H, L : G \to G$ be bounded linear maps, and let $\langle v, H v \rangle =
\langle v, L v \rangle$ for every $v \in \ker A$. Then there is $\sigma_{\min} \ge 0$ such that,
for every $\sigma > \sigma_{\min}$,
$$\langle v, H v \rangle + \sigma \|A v\|^2 > 0 \text{ for all } v \neq 0$$
if and only if $\langle v, L v \rangle > 0$ for all nonzero $v \in \ker A$.

Terms of the Hessian that vanish on $\ker A$ do not change the reduced test, and a large penalty
term gives positive curvature in the other directions. -/
theorem theorem_14_6_1_quadratic_test [FiniteDimensional ℝ G]
    (A : G →L[ℝ] F) (H L : G →L[ℝ] G)
    (hker : ∀ v, A v = 0 → ⟪v, H v⟫ = ⟪v, L v⟫) :
    ∃ σmin ≥ 0, ∀ σ > σmin,
      (∀ v ≠ (0 : G), 0 < ⟪v, H v⟫ + σ * ‖A v‖ ^ 2) ↔
        (∀ v ≠ (0 : G), A v = 0 → 0 < ⟪v, L v⟫) := by
  classical
  let q : G → ℝ := fun v ↦ ⟪v, H v⟫
  let S := Metric.sphere (0 : G) 1 ∩ {v | q v ≤ 0}
  have hq : Continuous q := continuous_id.inner H.continuous
  have hS : IsCompact S := (isCompact_sphere _ _).inter_right (isClosed_le hq continuous_const)
  have hunit (v : G) (hv : v ∈ S) : ‖v‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using hv.1
  have hforward (σ : ℝ) (h : ∀ v ≠ (0 : G), 0 < q v + σ * ‖A v‖ ^ 2)
      (v : G) (hv : v ≠ 0) (hAv : A v = 0) : 0 < ⟪v, L v⟫ := by
    have hh := h v hv
    change 0 < ⟪v, H v⟫ + σ * ‖A v‖ ^ 2 at hh
    simpa [hker v hAv, hAv] using hh
  by_cases hk : ∀ v ≠ (0 : G), A v = 0 → 0 < ⟪v, L v⟫
  · have hunit_pos : ∃ σmin ≥ 0, ∀ σ > σmin, ∀ v : G, ‖v‖ = 1 →
        0 < q v + σ * ‖A v‖ ^ 2 := by
      by_cases hne : S.Nonempty
      · obtain ⟨w, hw, hmin⟩ := hS.exists_isMinOn hne
          ((A.continuous.norm.pow 2).continuousOn)
        have hAw : A w ≠ 0 := by
          intro hz
          have hn : w ≠ 0 := by
            intro he
            have h := hunit w hw
            simp [he] at h
          have hle : q w ≤ 0 := hw.2
          exact (not_lt_of_ge hle) (by simpa only [q, hker w hz] using hk w hn hz)
        let d := ‖A w‖ ^ 2
        have hd : 0 < d := sq_pos_of_pos (norm_pos_iff.mpr hAw)
        refine ⟨‖H‖ / d, div_nonneg (norm_nonneg _) hd.le, fun σ hσ v hv ↦ ?_⟩
        have hσpos : 0 < σ := (div_nonneg (norm_nonneg _) hd.le).trans_lt hσ
        by_cases hvS : v ∈ S
        · have hlow : -‖H‖ ≤ q v := by
            have hi := (abs_le.mp (abs_real_inner_le_norm v (H v))).1
            have hop := H.le_opNorm v
            rw [hv, one_mul] at hi
            rw [hv, mul_one] at hop
            change -‖H‖ ≤ ⟪v, H v⟫
            linarith only [hi, hop]
          have hdv : d ≤ ‖A v‖ ^ 2 := hmin hvS
          have hprod : ‖H‖ < σ * d := (div_lt_iff₀ hd).mp hσ
          exact add_pos_of_nonneg_of_pos (show 0 ≤ q v + ‖H‖ by linarith)
            (show 0 < σ * ‖A v‖ ^ 2 - ‖H‖ by
              have hh := mul_le_mul_of_nonneg_left hdv hσpos.le
              linarith) |>.trans_eq (by ring)
        · have hqv : 0 < q v := by
            by_contra! he
            exact hvS ⟨by simpa [Metric.mem_sphere, dist_zero_right] using hv, he⟩
          exact add_pos_of_pos_of_nonneg hqv (mul_nonneg hσpos.le (sq_nonneg _))
      · refine ⟨0, le_rfl, fun σ hσ v hv ↦ ?_⟩
        have hqv : 0 < q v := by
          by_contra! he
          exact hne ⟨v, by simpa [Metric.mem_sphere, dist_zero_right] using hv, he⟩
        exact add_pos_of_pos_of_nonneg hqv (mul_nonneg hσ.le (sq_nonneg _))
    obtain ⟨σmin, hσmin, hpos⟩ := hunit_pos
    refine ⟨σmin, hσmin, fun σ hσ ↦ ⟨hforward σ, fun _ v hv ↦ ?_⟩⟩
    let r := ‖v‖⁻¹
    have hr : 0 < r := inv_pos.mpr (norm_pos_iff.mpr hv)
    have hnormalized : ‖r • v‖ = 1 := by
      rw [norm_smul, Real.norm_of_nonneg hr.le, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
    have hh := hpos σ hσ (r • v) hnormalized
    dsimp only [q] at hh
    rw [map_smul, real_inner_smul_left, real_inner_smul_right, map_smul, norm_smul,
      Real.norm_of_nonneg hr.le, mul_pow] at hh
    have hfact : r * (r * ⟪v, H v⟫) + σ * (r ^ 2 * ‖A v‖ ^ 2) =
        r ^ 2 * (⟪v, H v⟫ + σ * ‖A v‖ ^ 2) := by ring
    rw [hfact] at hh
    exact pos_of_mul_pos_right hh (sq_nonneg _)
  · exact ⟨0, le_rfl, fun σ _ ↦ ⟨hforward σ, fun h ↦ (hk h).elim⟩⟩

private theorem gradient_penalty_with_multiplier {f : G → ℝ} {c y : G → F} {x : G}
    (hf : DifferentiableAt ℝ f x) (hc : DifferentiableAt ℝ c x)
    (hy : DifferentiableAt ℝ y x) (σ : ℝ) :
    gradient (fun z ↦ lagrangian f c (y z) z + σ / 2 * ‖c z‖ ^ 2) x =
      gradient f x - (fderiv ℝ c x).adjoint (y x - σ • c x) -
        (fderiv ℝ y x).adjoint (c x) := by
  have hp := (hf.hasFDerivAt.sub (hy.hasFDerivAt.inner ℝ hc.hasFDerivAt)).add
    (hc.hasFDerivAt.norm_sq.const_mul (σ / 2))
  change HasFDerivAt (fun z ↦ lagrangian f c (y z) z + σ / 2 * ‖c z‖ ^ 2) _ _ at hp
  apply ext_inner_right ℝ
  intro d
  rw [inner_gradient_left, hp.fderiv, inner_sub_left, inner_sub_left, inner_gradient_left,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
  simp [inner_sub_left, real_inner_smul_left]
  rw [real_inner_comm (c x) ((fderiv ℝ y x) d)]
  ring

/-- **Equation (14.6.3)** of [conn2000trust]. Let $F$ be finite-dimensional, let $f$ and $c$ be
twice continuously differentiable, and let $c'(x)$ be surjective. Then
$$\nabla_x \phi(x, \sigma) = \nabla_x \ell\big(x, y(x) - \sigma c(x)\big) - y'(x)^* c(x),$$
where the multiplier $y(x) - \sigma c(x)$ is held fixed in the gradient of the Lagrangian. -/
theorem gradient_smoothExactPenalty_eq [FiniteDimensional ℝ F]
    {f : G → ℝ} {c : G → F} (hf : ContDiff ℝ 2 f) (hc : ContDiff ℝ 2 c)
    {x : G} (hfull : Function.Surjective (fderiv ℝ c x)) (σ : ℝ) :
    let y := fun z ↦ leastSquaresMultiplier (fderiv ℝ c z) (gradient f z)
    gradient (smoothExactPenalty f c σ) x =
      gradient (lagrangian f c (y x - σ • c x)) x - (fderiv ℝ y x).adjoint (c x) := by
  dsimp only
  let y := fun z ↦ leastSquaresMultiplier (fderiv ℝ c z) (gradient f z)
  have hy : DifferentiableAt ℝ y x :=
    (lemma_14_2_1 hf hc (multiplierGram_isUnit_of_surjective hfull)).1
  have hf' := hf.differentiable (by norm_num) x
  have hc' := hc.differentiable (by norm_num) x
  exact (gradient_penalty_with_multiplier hf' hc' hy σ).trans (by
    rw [gradient_lagrangian_eq hf' hc'])

/-- **Equation (14.6.4)** of [conn2000trust]. Let $F$ be finite-dimensional, let $f$ and $c$ be
three times continuously differentiable, and let $A = c'(x)$ be surjective. Let $D = y'(x)$.
Then
$$\nabla_{xx} \phi(x, \sigma) = \nabla_{xx} \ell\big(x, y(x) - \sigma c(x)\big) - A^* D - D^*
  A + \sigma A^* A - \frac{d}{dz} \Big[ y'(z)^* c(x) \Big]_{z = x},$$
where the residual $c(x)$ is held fixed in the last term.

**Correction.** The printed formula omits the last term, the derivative of the adjoint of $y'$
applied to the fixed residual. The term vanishes at a feasible point, but not in general; see
`ConnGouldToint.Chapter14.smoothExactPenalty_printed_hessian_counterexample`.

Off the feasible set, three continuous derivatives of the data are enough. -/
theorem fderiv_gradient_smoothExactPenalty_eq [FiniteDimensional ℝ F]
    {f : G → ℝ} {c : G → F} (hf : ContDiff ℝ 3 f) (hc : ContDiff ℝ 3 c)
    {x : G} (hfull : Function.Surjective (fderiv ℝ c x)) (σ : ℝ) :
    let A := fderiv ℝ c x
    let y := fun z ↦ leastSquaresMultiplier (fderiv ℝ c z) (gradient f z)
    let D := fderiv ℝ y x
    fderiv ℝ (gradient (smoothExactPenalty f c σ)) x =
      fderiv ℝ (gradient (lagrangian f c (y x - σ • c x))) x -
        A.adjoint.comp D - D.adjoint.comp A + σ • A.adjoint.comp A -
        fderiv ℝ (fun z ↦ (fderiv ℝ y z).adjoint (c x)) x := by
  dsimp only
  let A := fderiv ℝ c
  let y := fun z ↦ leastSquaresMultiplier (A z) (gradient f z)
  let Adj : (G →L[ℝ] F) →L[ℝ] (F →L[ℝ] G) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ)).toContinuousLinearEquiv.toContinuousLinearMap
  have hg : ContDiff ℝ 2 (gradient f) :=
    (InnerProductSpace.toDual ℝ G).symm.toContinuousLinearEquiv.contDiff.comp
      (hf.fderiv_right (by norm_num))
  have hA : ContDiff ℝ 2 A := hc.fderiv_right (by norm_num)
  have hy : ContDiffAt ℝ 2 y x := leastSquaresMultiplier_contDiffAt
    hA.contDiffAt hg.contDiffAt (multiplierGram_isUnit_of_surjective hfull)
  have hAdj : HasFDerivAt (fun z ↦ (A z).adjoint)
      (fderiv ℝ (fun z ↦ (A z).adjoint) x) x :=
    ((Adj.contDiff.comp hA).differentiable (by norm_num) x).hasFDerivAt
  have hg' := (hg.differentiable (by norm_num) x).hasFDerivAt
  have hf' := hf.differentiable (by norm_num)
  have hc' := hc.differentiable (by norm_num)
  have hy' := (hy.differentiableAt (by norm_num)).hasFDerivAt
  have hD : DifferentiableAt ℝ (fun z ↦ (fderiv ℝ y z).adjoint) x :=
    Adj.differentiableAt.comp x ((hy.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero)
  have heq : gradient (smoothExactPenalty f c σ) =ᶠ[𝓝 x] fun z ↦
      gradient f z - (A z).adjoint (y z - σ • c z) - (fderiv ℝ y z).adjoint (c z) := by
    filter_upwards [hy.eventually (by simp)] with z hz
    exact gradient_penalty_with_multiplier (hf' z) (hc' z) (hz.differentiableAt (by norm_num)) σ
  have hp := ((hg'.sub (hAdj.clm_apply (hy'.sub ((hc' x).hasFDerivAt.const_smul σ)))).sub
    (hD.hasFDerivAt.clm_apply (hc' x).hasFDerivAt)).congr_of_eventuallyEq heq
  have hL := (hg'.sub (hAdj.clm_apply (hasFDerivAt_const (y x - σ • c x) x))).congr_of_eventuallyEq
    (f₁ := gradient (lagrangian f c (y x - σ • c x)))
      (Filter.Eventually.of_forall fun z ↦ gradient_lagrangian_eq (hf' z) (hc' z) (y x - σ • c x))
  have hExtra := hD.hasFDerivAt.clm_apply (hasFDerivAt_const (c x) x)
  change fderiv ℝ (gradient (smoothExactPenalty f c σ)) x =
    fderiv ℝ (gradient (lagrangian f c (y x - σ • c x))) x -
      (A x).adjoint.comp (fderiv ℝ y x) - (fderiv ℝ y x).adjoint.comp (A x) +
        σ • (A x).adjoint.comp (A x) -
        fderiv ℝ (fun z ↦ (fderiv ℝ y z).adjoint (c x)) x
  rw [hp.fderiv, hL.fderiv, hExtra.fderiv]
  apply ContinuousLinearMap.ext
  intro d
  simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply, zero_apply,
    ContinuousLinearMap.flip_apply, smul_apply, map_sub, map_zero, map_smul, zero_add,
    Pi.sub_apply, Pi.smul_apply, A]
  abel

/-- Counterexample to the printed formula (14.6.4) of [conn2000trust] at an infeasible point. Let
$f(x) = x^3$ and $c(x) = x$ on $\mathbb{R}$, and $\sigma = 1$. At $x = 1$, where $c'(1)$ is
surjective, the Hessian of $\phi$ differs from the printed expression
$$\nabla_{xx} \ell\big(1, y(1) - c(1)\big) - A^* D - D^* A + A^* A.$$
-/
theorem smoothExactPenalty_printed_hessian_counterexample :
    let f := fun z : ℝ ↦ z ^ 3
    let c := fun z : ℝ ↦ z
    let x : ℝ := 1
    let A := fderiv ℝ c x
    let y := fun z ↦ leastSquaresMultiplier (fderiv ℝ c z) (gradient f z)
    let D := fderiv ℝ y x
    fderiv ℝ (gradient (smoothExactPenalty f c 1)) x ≠
      fderiv ℝ (gradient (lagrangian f c (y x - c x))) x -
        A.adjoint.comp D - D.adjoint.comp A + A.adjoint.comp A := by
  let f := fun z : ℝ ↦ z ^ 3
  let c := fun z : ℝ ↦ z
  let y := fun z ↦ leastSquaresMultiplier (fderiv ℝ c z) (gradient f z)
  have hA (z : ℝ) : fderiv ℝ c z = 1 := (hasFDerivAt_id z).fderiv
  have hy : y = fun z ↦ 3 * z ^ 2 := by
    funext z
    have hd : HasDerivAt f (3 * z ^ 2) z := by
      have hp := (hasDerivAt_id z).pow 3
      change HasDerivAt f ((3 : ℝ) * z ^ 2 * 1) z at hp
      simpa only [mul_one] using hp
    have hGram : multiplierGram (1 : ℝ →L[ℝ] ℝ) = 1 := by
      simp [multiplierGram, ContinuousLinearMap.one_def, ContinuousLinearMap.adjoint_id]
    simp [y, hA, leastSquaresMultiplier, hGram, gradient_eq_deriv', hd.deriv]
  have hextra :
      (fun z ↦ (fderiv ℝ y z).adjoint (c 1)) = fun z ↦ 6 * z := by
    funext z
    have hd : HasDerivAt y (6 * z) z := by
      rw [hy]
      have hp := ((hasDerivAt_id z).pow 2).const_mul (3 : ℝ)
      change HasDerivAt (fun w : ℝ ↦ 3 * w ^ 2) (3 * (2 * z ^ 1 * 1)) z at hp
      convert hp using 1
      ring
    have hAdj (L : ℝ →L[ℝ] ℝ) : L.adjoint 1 = L 1 := by
      simpa [real_inner_comm] using
        (ContinuousLinearMap.adjoint_inner_left (𝕜 := ℝ) L (1 : ℝ) (1 : ℝ))
    rw [show c 1 = 1 from rfl, hAdj, fderiv_apply_one_eq_deriv, hd.deriv]
  have hextra' : fderiv ℝ (fun z ↦ (fderiv ℝ y z).adjoint (c 1)) 1 (1 : ℝ) = 6 := by
    rw [hextra, fderiv_apply_one_eq_deriv]
    exact (show HasDerivAt (fun z : ℝ ↦ 6 * z) (6 * 1) 1 from
      (hasDerivAt_id (1 : ℝ)).const_mul 6).deriv.trans (mul_one 6)
  have hf : ContDiff ℝ 3 f := contDiff_id.pow 3
  have hc : ContDiff ℝ 3 c := contDiff_id
  have hsurj : Function.Surjective (fderiv ℝ c 1) := by
    rw [hA]
    exact Function.surjective_id
  have he := fderiv_gradient_smoothExactPenalty_eq hf hc hsurj 1
  dsimp only at he ⊢
  change fderiv ℝ (gradient (smoothExactPenalty f c 1)) 1 ≠
    fderiv ℝ (gradient (lagrangian f c (y 1 - c 1))) 1 -
      (fderiv ℝ c 1).adjoint.comp (fderiv ℝ y 1) -
      (fderiv ℝ y 1).adjoint.comp (fderiv ℝ c 1) + (fderiv ℝ c 1).adjoint.comp (fderiv ℝ c 1)
  change _ = fderiv ℝ (gradient (lagrangian f c (y 1 - 1 • c 1))) 1 - _ - _ +
    1 • (fderiv ℝ c 1).adjoint.comp (fderiv ℝ c 1) -
    fderiv ℝ (fun z ↦ (fderiv ℝ y z).adjoint (c 1)) 1 at he
  simp only [one_smul] at he
  rw [he]
  intro h
  have hh := congrArg (fun L : ℝ →L[ℝ] ℝ ↦ L 1) h
  simp only [sub_apply, hextra', y] at hh
  linarith

omit [CompleteSpace G] [CompleteSpace F] in
private theorem hasFDerivAt_apply_of_continuous_at_zero {M : G → F →L[ℝ] G} {c : G → F} {x : G} {A : G →L[ℝ] F}
    (hM : ContinuousAt M x) (hc : HasFDerivAt c A x) (hx : c x = 0) :
    HasFDerivAt (fun z ↦ M z (c z)) ((M x).comp A) x := by
  have hm : Tendsto (fun z ↦ ‖M z - M x‖) (𝓝 x) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hM
  have ho := (isLittleO_one_iff ℝ).mpr hm
  have hb : (fun z ↦ ‖c z‖) =O[𝓝 x] (fun z ↦ z - x) := by
    simpa only [hx, sub_zero] using hc.isBigO_sub.norm_left
  have hp := ho.mul_isBigO hb.norm_right
  have he : (fun z ↦ (M z - M x) (c z)) =o[𝓝 x] (fun z ↦ z - x) := by
    apply IsLittleO.of_bound
    intro ε hε
    filter_upwards [hp.bound hε] with z hz
    exact ((M z - M x).le_opNorm (c z)).trans (by
      simpa only [Pi.mul_apply, Pi.one_apply, one_mul, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg (z - x)), abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))] using hz)
  have hd : HasFDerivAt (fun z ↦ (M z - M x) (c z)) (0 : G →L[ℝ] G) x := by
    apply hasFDerivAt_iff_isLittleO.mpr
    simpa only [sub_self, zero_apply, sub_zero] using he
  convert ((M x).hasFDerivAt.comp x hc).add hd using 1
  · funext z
    simp only [Pi.add_apply, Function.comp_apply, sub_apply]
    abel
  · simp

/-- **Equation (14.6.4)** of [conn2000trust] at a feasible point. Let $F$ be finite-dimensional, let
$f$ and $c$ be twice continuously differentiable, let $c(x) = 0$, and let $A = c'(x)$ be
surjective. With $D = y'(x)$,
$$\nabla_{xx} \phi(x, \sigma) = \nabla_{xx} \ell\big(x, y(x)\big) - A^* D - D^* A + \sigma A^*
  A.$$

The multiplier map needs only one continuous derivative here, since the factor $c(x)$ of its
adjoint derivative vanishes. Away from the feasible set, the formula needs the extra term of
`ConnGouldToint.Chapter14.fderiv_gradient_smoothExactPenalty_eq`. -/
theorem fderiv_gradient_smoothExactPenalty_at_feasible [FiniteDimensional ℝ F]
    {f : G → ℝ} {c : G → F} (hf : ContDiff ℝ 2 f) (hc : ContDiff ℝ 2 c)
    {x : G} (hx : c x = 0) (hfull : Function.Surjective (fderiv ℝ c x)) (σ : ℝ) :
    let A := fderiv ℝ c x
    let y := fun z ↦ leastSquaresMultiplier (fderiv ℝ c z) (gradient f z)
    let D := fderiv ℝ y x
    fderiv ℝ (gradient (smoothExactPenalty f c σ)) x =
      fderiv ℝ (gradient (lagrangian f c (y x))) x -
        A.adjoint.comp D - D.adjoint.comp A + σ • A.adjoint.comp A := by
  dsimp only
  let A := fderiv ℝ c
  let y := fun z ↦ leastSquaresMultiplier (A z) (gradient f z)
  let Adj : (G →L[ℝ] F) →L[ℝ] (F →L[ℝ] G) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ)).toContinuousLinearEquiv.toContinuousLinearMap
  have hg : ContDiff ℝ 1 (gradient f) :=
    (InnerProductSpace.toDual ℝ G).symm.toContinuousLinearEquiv.contDiff.comp
      (hf.fderiv_right (by norm_num))
  have hA : ContDiff ℝ 1 (fun z ↦ (A z).adjoint) := Adj.contDiff.comp
    (hc.fderiv_right (by norm_num))
  have hy : ContDiffAt ℝ 1 y x := leastSquaresMultiplier_contDiffAt
    (hc.contDiffAt.fderiv_right (by norm_num)) hg.contDiffAt
    (multiplierGram_isUnit_of_surjective hfull)
  have hD : ContinuousAt (fun z ↦ (fderiv ℝ y z).adjoint) x :=
    Adj.continuous.continuousAt.comp (hy.continuousAt_fderiv one_ne_zero)
  have hAdj := (hA.differentiable one_ne_zero x).hasFDerivAt
  have hg' := (hg.differentiable one_ne_zero x).hasFDerivAt
  have hc' := (hc.differentiable (by norm_num) x).hasFDerivAt
  have hy' := (hy.differentiableAt one_ne_zero).hasFDerivAt
  have hdy := hasFDerivAt_apply_of_continuous_at_zero hD hc' hx
  have heq : gradient (smoothExactPenalty f c σ) =ᶠ[𝓝 x] fun z ↦
      gradient f z - (A z).adjoint (y z - σ • c z) - (fderiv ℝ y z).adjoint (c z) := by
    filter_upwards [hy.eventually (by simp)] with z hz
    exact gradient_penalty_with_multiplier
      (hf.differentiable (by norm_num) z) (hc.differentiable (by norm_num) z)
      (hz.differentiableAt one_ne_zero) σ
  have hp := ((hg'.sub (hAdj.clm_apply (hy'.sub (hc'.const_smul σ)))).sub
    hdy).congr_of_eventuallyEq heq
  have hL := (hg'.sub (hAdj.clm_apply (hasFDerivAt_const (y x) x))).congr_of_eventuallyEq
    (f₁ := gradient (lagrangian f c (y x)))
      (Filter.Eventually.of_forall fun z ↦ gradient_lagrangian_eq
        (hf.differentiable (by norm_num) z) (hc.differentiable (by norm_num) z) (y x))
  change fderiv ℝ (gradient (smoothExactPenalty f c σ)) x =
    fderiv ℝ (gradient (lagrangian f c (y x))) x -
      (A x).adjoint.comp (fderiv ℝ y x) - (fderiv ℝ y x).adjoint.comp (A x) +
        σ • (A x).adjoint.comp (A x)
  rw [hp.fderiv, hL.fderiv]
  apply ContinuousLinearMap.ext
  intro d
  simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply, zero_apply,
    ContinuousLinearMap.flip_apply, smul_apply, map_sub, map_zero, map_smul, zero_add,
    Pi.sub_apply, Pi.smul_apply, hx, smul_zero, sub_zero]
  abel

/-- **Theorem 14.6.1** of [conn2000trust]. Let $G$ and $F$ be finite-dimensional, let $f$ and $c$ be
twice continuously differentiable, let $c(x) = 0$, and let $A = c'(x)$ be surjective. Let
$y = y^{LS}(x)$. Then there is $\sigma_{\min} \ge 0$ such that, for every
$\sigma > \sigma_{\min}$, the Hessian $\nabla_{xx} \phi(x, \sigma)$ is positive definite if and
only if
$$\langle v, \nabla_{xx} \ell(x, y)\, v \rangle > 0 \quad\text{for all nonzero } v \in \ker A.$$

The corresponding first-order statement is (14.6.6). -/
theorem theorem_14_6_1 [FiniteDimensional ℝ G] [FiniteDimensional ℝ F]
    {f : G → ℝ} {c : G → F} (hf : ContDiff ℝ 2 f) (hc : ContDiff ℝ 2 c)
    {x : G} (hx : c x = 0) (hfull : Function.Surjective (fderiv ℝ c x)) :
    let A := fderiv ℝ c x
    let y := leastSquaresMultiplier A (gradient f x)
    ∃ σmin ≥ 0, ∀ σ > σmin,
      (∀ v ≠ (0 : G), 0 < ⟪v, fderiv ℝ (gradient (smoothExactPenalty f c σ)) x v⟫) ↔
        (∀ v ≠ (0 : G), A v = 0 →
          0 < ⟪v, fderiv ℝ (gradient (lagrangian f c y)) x v⟫) := by
  dsimp only
  let A := fderiv ℝ c x
  let y := fun z ↦ leastSquaresMultiplier (fderiv ℝ c z) (gradient f z)
  let L := fderiv ℝ (gradient (lagrangian f c (y x))) x
  let D := fderiv ℝ y x
  let H := L - A.adjoint.comp D - D.adjoint.comp A
  have hker (v : G) (hv : A v = 0) : ⟪v, H v⟫ = ⟪v, L v⟫ := by
    simp only [H, sub_apply, ContinuousLinearMap.comp_apply, inner_sub_right,
      ContinuousLinearMap.adjoint_inner_right, hv, inner_zero_left, inner_zero_right, sub_zero]
  obtain ⟨m, hm, h⟩ := theorem_14_6_1_quadratic_test A H L hker
  refine ⟨m, hm, fun σ hσ ↦ ?_⟩
  have he (v : G) : ⟪v, fderiv ℝ (gradient (smoothExactPenalty f c σ)) x v⟫ =
      ⟪v, H v⟫ + σ * ‖A v‖ ^ 2 := by
    have hh := fderiv_gradient_smoothExactPenalty_at_feasible hf hc hx hfull σ
    change fderiv ℝ (gradient (smoothExactPenalty f c σ)) x =
      H + σ • A.adjoint.comp A at hh
    rw [hh, add_apply, smul_apply, inner_add_right, real_inner_smul_right,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
      real_inner_self_eq_norm_sq]
  simpa only [he] using h σ hσ

end ConnGouldToint.Chapter14
