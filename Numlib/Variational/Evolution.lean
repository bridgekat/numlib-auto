/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Numlib.Analysis.ODE.Gronwall
import Numlib.Approximation.BrokenPolynomial
import Numlib.Projection.OneDimensional
import Numlib.Variational.Galerkin
import Numlib.Variational.LaxMilgram

/-!
# Galerkin semi-discretizations of evolution problems and the θ-method

This module studies Galerkin semi-discretizations of linear evolution problems and their
discretization in time by the θ-method, following Chapter 13 of [quarteroni2000numerical]. The
setting is a real inner product space $K$, which in the applications is a finite-dimensional trial
space with the $L^2$ inner product, a family of bounded bilinear forms $a(t)$ on $K$ (the spatial
operator) and a family of bounded functionals $F(t)$ (the source). The semi-discrete problem is the
linear differential equation $\langle u'(t), v \rangle + a(t)(u(t), v) = F(t)(v)$ for all $v \in K$
((13.13), (13.65) and (13.68) of [quarteroni2000numerical]). Every energy estimate of §13.1, §13.3
and §13.10 of the book follows from the identity
$$\frac{d}{dt} \|u(t)\|^2 = 2 \big(F(t)(u(t)) - a(t)(u(t), u(t))\big).$$
Under $L^2$-coercivity $\gamma \|v\|^2 \le a(v, v)$ it gives **exponential decay**, as for the heat
equation with $\gamma = \nu / C_P^2$ from the Poincaré inequality. Under
$\mu_0 \|v\|^2 + \frac12 Q(v) \le a(v, v)$ with a functional $Q$ for boundary or jump terms, it
gives **dissipation**, as for the transport equation with the outflow term $a(\beta) u(\beta)^2$ and
the jump terms of the discontinuous Galerkin method. Under
$-m(t) \|v\|^2 + \frac12 Q(v) \le a(v, v)$, when the reaction term has the wrong sign, it gives
**growth of Gronwall type**.

The θ-method is $\langle (u^+ - u) / \Delta t, v \rangle + a(\theta u^+ + (1 - \theta) u, v) =
\theta \ell_1(v) + (1 - \theta) \ell_0(v)$ ((13.17)). Its energy identity $\frac12 (\|u^+\|^2 -
\|u\|^2) = -\Delta t \, a(w, w) - (\theta - \frac12) \|u^+ - u\|^2$ with
$w = \theta u^+ + (1 - \theta) u$ needs no symmetry of $a$. For a positive form it gives
unconditional stability for $\theta \ge \frac12$ and the telescoped estimates of backward Euler,
also for the nonsymmetric transport forms. For a symmetric coercive form, the eigenpairs of the form
relative to the inner product (Definition 13.1 and (13.22)) give an orthonormal basis. In each
eigenvector direction the step multiplies the coordinate by $r_\theta(\lambda \Delta t) = (1 - (1 -
\theta) \lambda \Delta t) / (1 + \theta \lambda \Delta t)$, so for $\theta < \frac12$ the step is
nonexpansive for every datum if and only if $(1 - 2\theta) \lambda_{\max} \Delta t \le 2$. The last
section defines the transport form and the upwind discontinuous Galerkin form for
$u_t + a u_x + a_0 u$ on the broken polynomial space of `Numlib.Approximation.BrokenPolynomial`
((13.68)) and proves their energy identities.

## Main definitions

* `Variational.IsSemidiscreteGalerkin`: the semi-discrete Galerkin problem.
* `Variational.IsThetaStep`: one step of the θ-method, as a relation between consecutive iterates.
* `Variational.IsFormEigenpair`: an eigenpair of a form relative to the inner product.
* `Variational.transportForm`, `Variational.dgUpwindForm`: the transport form and the upwind
  discontinuous Galerkin form on a broken polynomial space.

## Main results

* `Variational.IsSemidiscreteGalerkin.hasDerivWithinAt_norm_sq`: the energy identity of the
  semi-discrete problem.
* `Variational.IsSemidiscreteGalerkin.norm_sq_le_exp`: exponential decay of the energy under
  $L^2$-coercivity.
* `Variational.IsSemidiscreteGalerkin.norm_sq_add_integral_le_integral`,
  `Variational.IsSemidiscreteGalerkin.norm_sq_add_integral_le`: the energy estimate in integrated
  form and the dissipative energy estimate.
* `Variational.IsSemidiscreteGalerkin.norm_sq_add_integral_le_exp`: the energy estimate of Gronwall
  type.
* `Variational.IsThetaStep.existsUnique`: the θ-step exists and is unique.
* `Variational.IsThetaStep.energy_identity`, `Variational.IsThetaStep.norm_le_of_half_le`: the
  energy identity of the θ-method and unconditional stability for $\theta \ge \frac12$.
* `Variational.IsThetaStep.norm_sq_add_sum_le`,
  `Variational.IsThetaStep.norm_sq_add_sum_le_of_coercive`,
  `Variational.IsThetaStep.norm_sq_add_sum_le_of_le`: the telescoped estimates of backward Euler,
  without and with sources.
* `Variational.exists_orthonormalBasis_isFormEigenpair`: a symmetric form on a finite-dimensional
  space has an orthonormal basis of eigenvectors.
* `Variational.IsThetaStep.inner_eq_of_isFormEigenpair`: the θ-method in an eigenvector direction.
* `Variational.IsThetaStep.norm_le_of_le_of_lt_half`,
  `Variational.IsThetaStep.forall_norm_le_iff_of_lt_half`: the stability condition
  $(1 - 2\theta) \lambda_{\max} \Delta t \le 2$, sufficient and necessary.
* `Variational.dgUpwindForm_apply_self`, `Variational.transportForm_apply_self_of_continuous`: the
  energy identities of the upwind and the transport forms.

## Proof outline

The three estimates of the semi-discrete problem are instances of the differential Gronwall
inequalities of `Numlib.Analysis.ODE.Gronwall`, with the derivative of the energy taken within
$[0, T]$. The integrated form `Variational.IsSemidiscreteGalerkin.norm_sq_add_integral_le_integral`
keeps a pointwise bound of the derivative as a hypothesis. The dissipative estimate is this form
after Young's inequality on the source. An estimate in which a boundary term, not coercivity,
absorbs the source, such as (13.69), where the jump at $x_0$ absorbs the inflow datum, needs the
integrated form directly.

The sufficient half of the stability condition for $\theta < \frac12$ does not use eigenvectors and
holds in any real Hilbert space. It follows from the operator Cauchy–Schwarz inequality $\|Bw\|^2
\le \lambda_{\max} \langle Bw, w \rangle$ for the positive symmetric operator $B$ of the form.
`Numlib.FiniteDifference.Parabolic` uses this argument in the inner product of the mass matrix.

## Implementation notes

* The θ-step is a relation, so that the implicit methods need no inverse in the definition. Its
  existence and uniqueness is the Lax–Milgram theorem for the form $\langle \cdot, \cdot \rangle +
  \theta \Delta t \, a$.
* No completeness of $K$ is assumed where none is used. The hypothesis `[CompleteSpace K]` appears
  exactly where the operator `SesqForm.toOperator a` of the form appears: the Lax–Milgram theorem,
  the description of eigenpairs by eigenvectors and the operator Cauchy–Schwarz inequality. The
  hypothesis `[FiniteDimensional ℝ K]` appears where the spectral theorem does.
* Positivity of a form is `a.IsCoerciveWith 0`, and coercivity is `a.IsCoerciveWith c`, as in the
  other `Numlib.Variational` modules.
* The time derivative is `HasDerivWithinAt u (u' t) (Icc 0 T) t`, which is one-sided at the
  endpoints. The derivative $u'$ is quantified existentially in the definition of the semi-discrete
  problem.
* The coefficients $a$ and $a_0$ of the transport forms are functions with a hypothesis of interval
  integrability, which makes the forms bilinear. The energy identities require $a$ to be
  differentiable with a continuous derivative, as the book does.
* The descriptions in coordinates, by mass and stiffness matrices, are in
  `Numlib.FiniteDifference.Parabolic`, which imports this module.
-/

open Set Filter Topology intervalIntegral Real
open scoped RealInnerProductSpace Matrix Interval
open MeasureTheory (volume)

noncomputable section

/-- The bounded form of a bilinear map $b$ on a finite-dimensional real inner product space $K$:
every bilinear map on $K$ is bounded, and `SesqForm.ofBilin b` is $b$ as a bounded form. -/
def SesqForm.ofBilin {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [FiniteDimensional ℝ K] (b : K →ₗ[ℝ] K →ₗ[ℝ] ℝ) : SesqForm ℝ K :=
  (LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (K →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (K →L[ℝ] ℝ)).toLinearMap ∘ₗ b) :
      K →L[ℝ] K →L[ℝ] ℝ)

/-- The bounded form of a bilinear map $b$ takes the value $b(u, v)$ at $(u, v)$. -/
@[simp]
theorem SesqForm.ofBilin_apply {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [FiniteDimensional ℝ K] (b : K →ₗ[ℝ] K →ₗ[ℝ] ℝ) (u v : K) : SesqForm.ofBilin b u v = b u v :=
  rfl

namespace Variational

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-! ### The semi-discrete Galerkin problem -/

/-- **The semi-discrete Galerkin problem** ([quarteroni2000numerical], (13.13); (13.65) and (13.68)
for the transport equation). Let $K$ be a real inner product space, let $a(t)$ be bounded
bilinear forms and $F(t)$ bounded functionals on $K$ for $t \in \mathbb{R}$, let $u_0 \in K$ and
$T \in \mathbb{R}$. A function $u \colon \mathbb{R} \to K$ is a solution if $u(0) = u_0$ and
there is a function $u'$ such that, for every $t \in [0, T]$, $u'(t)$ is the derivative of $u$
at $t$ within $[0, T]$ and
$$\langle u'(t), v \rangle + a(t)(u(t), v) = F(t)(v) \quad \text{for all } v \in K.$$

With $K$ the whole space, this is the weak formulation (13.12) itself. The derivative within
$[0, T]$ is one-sided at the endpoints. -/
def IsSemidiscreteGalerkin (a : ℝ → SesqForm ℝ K) (F : ℝ → K →L[ℝ] ℝ) (u₀ : K) (T : ℝ)
    (u : ℝ → K) : Prop :=
  u 0 = u₀ ∧ ∃ u' : ℝ → K, ∀ t ∈ Icc 0 T,
    HasDerivWithinAt u (u' t) (Icc 0 T) t ∧ ∀ v, ⟪u' t, v⟫ + a t (u t) v = F t v

namespace IsSemidiscreteGalerkin

variable {a : ℝ → SesqForm ℝ K} {F : ℝ → K →L[ℝ] ℝ} {u₀ : K} {T : ℝ} {u : ℝ → K}

/-- **The energy identity.** Let $u$ solve the semi-discrete problem and let $t \in [0, T]$. Then
the derivative of $\|u\|^2$ at $t$ within $[0, T]$ is
$$\frac{d}{dt} \|u(t)\|^2 = 2 \big(F(t)(u(t)) - a(t)(u(t), u(t))\big).$$

The proof is `HasDerivWithinAt.norm_sq` and the equation tested with $v = u(t)$. Every energy
estimate of the module integrates this identity. -/
theorem hasDerivWithinAt_norm_sq (h : IsSemidiscreteGalerkin a F u₀ T u) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun t => ‖u t‖ ^ 2) (2 * (F t (u t) - a t (u t) (u t))) (Icc 0 T) t := by
  obtain ⟨u', hu'⟩ := h.2
  obtain ⟨hd, heq⟩ := hu' t ht
  have key := hd.norm_sq
  have : ⟪u t, u' t⟫ = F t (u t) - a t (u t) (u t) := by
    rw [real_inner_comm, ← heq (u t)]; ring
  rwa [this] at key

/-- A solution of the semi-discrete problem is continuous on $[0, T]$. -/
theorem continuousOn (h : IsSemidiscreteGalerkin a F u₀ T u) : ContinuousOn u (Icc 0 T) := by
  obtain ⟨u', hu'⟩ := h.2
  exact fun t ht => (hu' t ht).1.continuousWithinAt

/-- For a solution $u$ of the semi-discrete problem, the function $t \mapsto \|u(t)\|^2$ is
continuous on $[0, T]$. -/
theorem continuousOn_norm_sq (h : IsSemidiscreteGalerkin a F u₀ T u) :
    ContinuousOn (fun t => ‖u t‖ ^ 2) (Icc 0 T) :=
  (continuous_norm.pow 2).comp_continuousOn h.continuousOn

/-- Let $u$ solve the semi-discrete problem and let $t \in [0, T)$. Then the derivative of $\|u\|^2$
at $t$ within $[t, \infty)$ is $2 (F(t)(u(t)) - a(t)(u(t), u(t)))$.

This is the one-sided form of the derivative that the Gronwall lemmas take. -/
theorem hasDerivWithinAt_norm_sq_Ici (h : IsSemidiscreteGalerkin a F u₀ T u) {t : ℝ}
    (ht : t ∈ Ico 0 T) :
    HasDerivWithinAt (fun t => ‖u t‖ ^ 2) (2 * (F t (u t) - a t (u t) (u t))) (Ici t) t :=
  (h.hasDerivWithinAt_norm_sq (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
    (Icc_mem_nhdsGE_of_mem ht)

omit [InnerProductSpace ℝ K] in
/-- **Young's inequality.** Let $\gamma > 0$ and $\varphi \in \mathbb{R}$. Then for every $v$ in a
normed group, $2 \varphi \|v\| \le \gamma \|v\|^2 + \varphi^2 / \gamma$.

This turns $2 F(u) \le 2 \|F\| \|u\|$ into a bound that coercivity can absorb. -/
theorem two_mul_mul_norm_le {γ : ℝ} (hγ : 0 < γ) (φ : ℝ) (v : K) :
    2 * φ * ‖v‖ ≤ γ * ‖v‖ ^ 2 + φ ^ 2 / γ := by
  have h := mul_nonneg hγ.le (sq_nonneg (‖v‖ - φ / γ))
  have : γ * (‖v‖ - φ / γ) ^ 2 = γ * ‖v‖ ^ 2 - 2 * φ * ‖v‖ + φ ^ 2 / γ := by
    field_simp
    ring
  linarith

/-- **The exponential energy estimate** ([quarteroni2000numerical], (13.7) and the estimate after
(13.13)). Let $u$ solve the semi-discrete problem. Let $\gamma > 0$ with
$\gamma \|v\|^2 \le a(t)(v, v)$ for all $t \in [0, T]$ and $v \in K$, and let $\varphi$ be
continuous on $[0, T]$ with $\|F(t)\| \le \varphi(t)$ for $t \in [0, T]$. Then for every
$t \in [0, T]$,
$$\|u(t)\|^2 \le e^{-\gamma t} \|u_0\|^2 + \gamma^{-1} \int_0^t e^{\gamma (s - t)} \varphi(s)^2
  \, ds.$$

The energy $E = \|u\|^2$ satisfies $E' = 2 F(u) - 2 a(u, u) \le 2 \varphi \|u\| - 2 \gamma E \le
-\gamma E + \varphi^2 / \gamma$, and the linear differential Gronwall inequality
`Gronwall.le_exp_neg_mul_add_integral_of_hasDerivWithinAt_le` integrates it. For the heat
equation, $\gamma = \nu / C_P^2$ with the Poincaré constant $C_P$, and
$\varphi(t) = \|f(t)\|_{L^2}$. -/
theorem norm_sq_le_exp (h : IsSemidiscreteGalerkin a F u₀ T u) {γ : ℝ} (hγ : 0 < γ)
    (hcoer : ∀ t ∈ Icc 0 T, (a t).IsCoerciveWith γ) {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc 0 T))
    (hF : ∀ t ∈ Icc 0 T, ‖F t‖ ≤ φ t) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖u t‖ ^ 2 ≤ exp (-γ * t) * ‖u₀‖ ^ 2 + γ⁻¹ * ∫ s in (0 : ℝ)..t, exp (γ * (s - t)) * φ s ^ 2 := by
  have bound : ∀ s ∈ Ico 0 T,
      2 * (F s (u s) - a s (u s) (u s)) ≤ -γ * ‖u s‖ ^ 2 + φ s ^ 2 / γ := by
    intro s hs
    have hs' : s ∈ Icc 0 T := Ico_subset_Icc_self hs
    have h1 : F s (u s) ≤ φ s * ‖u s‖ :=
      (le_abs_self _).trans (((F s).le_opNorm (u s)).trans
        (mul_le_mul_of_nonneg_right (hF s hs') (norm_nonneg _)))
    have h2 : γ * ‖u s‖ ^ 2 ≤ a s (u s) (u s) := hcoer s hs' (u s)
    have h3 := two_mul_mul_norm_le hγ (φ s) (u s)
    linarith
  have key := Gronwall.le_exp_neg_mul_add_integral_of_hasDerivWithinAt_le
    (g := fun s => φ s ^ 2 / γ) h.continuousOn_norm_sq
    (fun s hs => h.hasDerivWithinAt_norm_sq_Ici hs) ((hφ.pow 2).div_const γ) bound ht
  rw [h.1, sub_zero] at key
  refine key.trans (le_of_eq ?_)
  rw [← integral_const_mul]
  congr 1
  exact integral_congr fun s _ => by ring

/-- **The energy estimate in integrated form.** Let $u$ solve the semi-discrete problem, and let $w$
and $g$ be continuous on $[0, T]$ with
$$2 \big(F(s)(u(s)) - a(s)(u(s), u(s))\big) + w(s) \le g(s) \quad \text{for all } s \in [0,
  T).$$
Then for every $t \in [0, T]$,
$$\|u(t)\|^2 + \int_0^t w(s) \, ds \le \|u_0\|^2 + \int_0^t g(s) \, ds.$$

The proof applies the variation-of-constants inequality with zero coefficient to
$\Phi(t) = \|u(t)\|^2 + \int_0^t w$. This is the common form of the estimates below:
`Variational.IsSemidiscreteGalerkin.norm_sq_add_integral_le` is this estimate after Young's
inequality on the source. The pointwise bound stays a hypothesis because some estimates absorb
the source by a boundary term, such as (13.69) of [quarteroni2000numerical], where the jump at
$x_0$ absorbs the inflow datum of the discontinuous Galerkin method and there is no bound
$\varphi$ of the source. -/
theorem norm_sq_add_integral_le_integral (h : IsSemidiscreteGalerkin a F u₀ T u) {w g : ℝ → ℝ}
    (hw : ContinuousOn w (Icc 0 T)) (hg : ContinuousOn g (Icc 0 T))
    (bound : ∀ s ∈ Ico 0 T, 2 * (F s (u s) - a s (u s) (u s)) + w s ≤ g s)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖u t‖ ^ 2 + ∫ s in (0 : ℝ)..t, w s ≤ ‖u₀‖ ^ 2 + ∫ s in (0 : ℝ)..t, g s := by
  set Φ : ℝ → ℝ := fun s => ‖u s‖ ^ 2 + ∫ q in (0 : ℝ)..s, w q with hΦ
  have hΦc : ContinuousOn Φ (Icc 0 T) :=
    h.continuousOn_norm_sq.add (intervalIntegral.continuousOn_integral_Icc hw)
  have hΦ' : ∀ s ∈ Ico 0 T, HasDerivWithinAt Φ
      (2 * (F s (u s) - a s (u s) (u s)) + w s) (Ici s) s := fun s hs =>
    (h.hasDerivWithinAt_norm_sq_Ici hs).add (intervalIntegral.hasDerivWithinAt_integral_Ici hw hs)
  have key := Gronwall.le_exp_integral_mul_of_hasDerivWithinAt_le (p := fun _ => (0 : ℝ)) (q := g)
    hΦc hΦ' continuousOn_const hg (fun s hs => by simpa using bound s hs) ht
  have h1 : ‖u 0‖ ^ 2 = ‖u₀‖ ^ 2 := by rw [h.1]
  simpa [hΦ, h1] using key

/-- **The dissipative energy estimate** ([quarteroni2000numerical], (13.66) and (13.69)). Let $u$
solve the semi-discrete problem. Let $\mu_0 > 0$, let $Q(t, \cdot)$ be functions on $K$ with
$t \mapsto Q(t, u(t))$ continuous on $[0, T]$, and assume
$$\mu_0 \|v\|^2 + \tfrac12 Q(t, v) \le a(t)(v, v) \quad \text{for all } t \in [0, T], \ v \in
  K.$$
Let $\varphi$ be continuous on $[0, T]$ with $\|F(t)\| \le \varphi(t)$ for $t \in [0, T]$. Then
for every $t \in [0, T]$,
$$\|u(t)\|^2 + \int_0^t \big(\mu_0 \|u(s)\|^2 + Q(s, u(s))\big) \, ds \le \|u_0\|^2 + \mu_0^{-1}
  \int_0^t \varphi(s)^2 \, ds.$$

In the applications, $Q$ is the outflow term $a(\beta) v(\beta)^2$ and the jump terms of the
discontinuous Galerkin form. No sign of $Q$ is needed. The proof bounds $E' + \mu_0 \|u\|^2 +
Q(u) \le \varphi^2 / \mu_0$ by Young's inequality and applies
`Variational.IsSemidiscreteGalerkin.norm_sq_add_integral_le_integral`. -/
theorem norm_sq_add_integral_le (h : IsSemidiscreteGalerkin a F u₀ T u) {μ₀ : ℝ} (hμ : 0 < μ₀)
    {Q : ℝ → K → ℝ} (hQc : ContinuousOn (fun t => Q t (u t)) (Icc 0 T))
    (hcoer : ∀ t ∈ Icc 0 T, ∀ v, μ₀ * ‖v‖ ^ 2 + Q t v / 2 ≤ a t v v)
    {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc 0 T)) (hF : ∀ t ∈ Icc 0 T, ‖F t‖ ≤ φ t)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖u t‖ ^ 2 + ∫ s in (0 : ℝ)..t, (μ₀ * ‖u s‖ ^ 2 + Q s (u s))
      ≤ ‖u₀‖ ^ 2 + μ₀⁻¹ * ∫ s in (0 : ℝ)..t, φ s ^ 2 := by
  have hwc : ContinuousOn (fun s => μ₀ * ‖u s‖ ^ 2 + Q s (u s)) (Icc 0 T) :=
    (continuousOn_const.mul h.continuousOn_norm_sq).add hQc
  have bound : ∀ s ∈ Ico 0 T,
      2 * (F s (u s) - a s (u s) (u s)) + (μ₀ * ‖u s‖ ^ 2 + Q s (u s)) ≤ φ s ^ 2 / μ₀ := by
    intro s hs
    have hs' : s ∈ Icc 0 T := Ico_subset_Icc_self hs
    have h1 : F s (u s) ≤ φ s * ‖u s‖ :=
      (le_abs_self _).trans (((F s).le_opNorm (u s)).trans
        (mul_le_mul_of_nonneg_right (hF s hs') (norm_nonneg _)))
    have h2 := hcoer s hs' (u s)
    have h3 := two_mul_mul_norm_le hμ (φ s) (u s)
    linarith
  refine (h.norm_sq_add_integral_le_integral (g := fun s => φ s ^ 2 / μ₀) hwc
    ((hφ.pow 2).div_const μ₀) bound ht).trans (le_of_eq ?_)
  rw [← integral_const_mul]
  congr 1
  exact integral_congr fun s _ => by ring

/-- **Energy dissipation without source** ([quarteroni2000numerical], §13.10.1, the conservation of
energy $\|u_h(t)\| \le \|u_{0h}\|$). Let $u$ solve the semi-discrete problem with $F(t) = 0$ for
all $t$, and let $a(t)(v, v) \ge 0$ for all $t \in [0, T]$ and $v \in K$. Then
$t \mapsto \|u(t)\|$ is antitone on $[0, T]$. In particular, $\|u(t)\| \le \|u_0\|$ for
$t \in [0, T]$. -/
theorem norm_le_of_nonneg (h : IsSemidiscreteGalerkin a F u₀ T u) (hF : ∀ t, F t = 0)
    (hpos : ∀ t ∈ Icc 0 T, (a t).IsCoerciveWith 0) :
    AntitoneOn (fun t => ‖u t‖) (Icc 0 T) := by
  have hsq : AntitoneOn (fun t => ‖u t‖ ^ 2) (Icc 0 T) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T) h.continuousOn_norm_sq
      (f' := fun t => 2 * (F t (u t) - a t (u t) (u t))) (fun t ht => ?_) fun t ht => ?_
    · exact (h.hasDerivWithinAt_norm_sq (interior_subset ht)).mono interior_subset
    · have := hpos t (interior_subset ht) (u t)
      simp only [zero_mul, RCLike.re_to_real] at this
      simp only [hF, zero_apply]
      linarith
  intro s hs t ht hst
  have := hsq hs ht hst
  simpa using pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero |>.1 this

/-- **The energy estimate of Gronwall type for a form that is not dissipative**
([quarteroni2000numerical], (13.67)). Let $u$ solve the semi-discrete problem. Let $m$ be
continuous on $[0, T]$ with $m \ge 0$ there, which stands for a reaction coefficient with the
wrong sign. Let $Q(t, v) \ge 0$ for all $t$ and $v$, with $t \mapsto Q(t, u(t))$ continuous on
$[0, T]$, and assume
$$-m(t) \|v\|^2 + \tfrac12 Q(t, v) \le a(t)(v, v) \quad \text{for all } t \in [0, T], \ v \in
  K.$$
Let $\varphi$ be continuous on $[0, T]$ with $\|F(t)\| \le \varphi(t)$ for $t \in [0, T]$. Then
for every $t \in [0, T]$,
$$\|u(t)\|^2 + \int_0^t Q(s, u(s)) \, ds \le \Big(\|u_0\|^2 + \int_0^t \varphi(s)^2 \, ds\Big)
  \exp \int_0^t (1 + 2 m(s)) \, ds.$$

The function $\Phi = \|u\|^2 + \int_0^t Q(u)$ satisfies $\Phi' \le (1 + 2m) \|u\|^2 + \varphi^2
\le (1 + 2m) \Phi + \varphi^2$, and `Gronwall.le_mul_exp_integral_of_hasDerivWithinAt_le`
integrates it. -/
theorem norm_sq_add_integral_le_exp (h : IsSemidiscreteGalerkin a F u₀ T u) {m : ℝ → ℝ}
    (hm : ContinuousOn m (Icc 0 T)) (hm0 : ∀ t ∈ Icc 0 T, 0 ≤ m t)
    {Q : ℝ → K → ℝ} (hQ0 : ∀ t v, 0 ≤ Q t v) (hQc : ContinuousOn (fun t => Q t (u t)) (Icc 0 T))
    (hcoer : ∀ t ∈ Icc 0 T, ∀ v, -(m t) * ‖v‖ ^ 2 + Q t v / 2 ≤ a t v v)
    {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc 0 T)) (hF : ∀ t ∈ Icc 0 T, ‖F t‖ ≤ φ t)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖u t‖ ^ 2 + ∫ s in (0 : ℝ)..t, Q s (u s)
      ≤ (‖u₀‖ ^ 2 + ∫ s in (0 : ℝ)..t, φ s ^ 2) * exp (∫ s in (0 : ℝ)..t, (1 + 2 * m s)) := by
  set Φ : ℝ → ℝ := fun s => ‖u s‖ ^ 2 + ∫ r in (0 : ℝ)..s, Q r (u r) with hΦ
  have hΦc : ContinuousOn Φ (Icc 0 T) :=
    h.continuousOn_norm_sq.add (intervalIntegral.continuousOn_integral_Icc hQc)
  have hΦ' : ∀ s ∈ Ico 0 T, HasDerivWithinAt Φ
      (2 * (F s (u s) - a s (u s) (u s)) + Q s (u s)) (Ici s) s := fun s hs =>
    (h.hasDerivWithinAt_norm_sq_Ici hs).add (intervalIntegral.hasDerivWithinAt_integral_Ici hQc hs)
  have bound : ∀ s ∈ Ico 0 T,
      2 * (F s (u s) - a s (u s) (u s)) + Q s (u s) ≤ (1 + 2 * m s) * Φ s + φ s ^ 2 := by
    intro s hs
    have hs' : s ∈ Icc 0 T := Ico_subset_Icc_self hs
    have h1 : F s (u s) ≤ φ s * ‖u s‖ :=
      (le_abs_self _).trans (((F s).le_opNorm (u s)).trans
        (mul_le_mul_of_nonneg_right (hF s hs') (norm_nonneg _)))
    have h2 := hcoer s hs' (u s)
    have h3 := two_mul_mul_norm_le one_pos (φ s) (u s)
    have h4 : 0 ≤ ∫ r in (0 : ℝ)..s, Q r (u r) :=
      integral_nonneg hs.1 fun r _ => hQ0 r (u r)
    have h5 : 0 ≤ 1 + 2 * m s := by linarith [hm0 s hs']
    have h6 : 0 ≤ (1 + 2 * m s) * ∫ r in (0 : ℝ)..s, Q r (u r) := mul_nonneg h5 h4
    simp only [hΦ, one_mul, div_one] at h3 ⊢
    nlinarith
  have key := Gronwall.le_mul_exp_integral_of_hasDerivWithinAt_le (p := fun s => 1 + 2 * m s)
    (g := fun s => φ s ^ 2) hΦc hΦ' (continuousOn_const.add (continuousOn_const.mul hm))
    (fun s hs => by linarith [hm0 s hs]) (hφ.pow 2) (fun s _ => sq_nonneg _) bound ht
  simpa only [hΦ, h.1, integral_same, add_zero] using key

end IsSemidiscreteGalerkin

/-! ### The θ-method -/

/-- **One step of the θ-method** ([quarteroni2000numerical], (13.17)). Let $a$ be a bounded bilinear
form on $K$, let $\theta, \Delta t \in \mathbb{R}$, and let $\ell_0$ and $\ell_1$ be bounded
functionals, the sources at the old and at the new time. A vector $u'$ is the θ-step of $u$ if
$$\Big\langle \frac{u' - u}{\Delta t}, v \Big\rangle + a(\theta u' + (1 - \theta) u, v) = \theta
  \ell_1(v) + (1 - \theta) \ell_0(v) \quad \text{for all } v \in K.$$

The values $\theta = 0$, $1$ and $\frac12$ give the forward Euler, the backward Euler and the
Crank–Nicolson methods. The step is a relation, so that the implicit methods need no inverse.
The quotient is `Δt⁻¹ • (u' - u)`, which is $0$ when $\Delta t = 0$. -/
def IsThetaStep (a : SesqForm ℝ K) (θ Δt : ℝ) (ℓ₀ ℓ₁ : K →L[ℝ] ℝ) (u u' : K) : Prop :=
  ∀ v, ⟪Δt⁻¹ • (u' - u), v⟫ + a (θ • u' + (1 - θ) • u) v = θ * ℓ₁ v + (1 - θ) * ℓ₀ v

namespace IsThetaStep

variable {a : SesqForm ℝ K} {θ Δt : ℝ} {ℓ₀ ℓ₁ : K →L[ℝ] ℝ} {u u' : K}

/-- Let $\Delta t \neq 0$. Then $u'$ is the θ-step of $u$ if and only if for every $v \in K$
$$\langle u', v \rangle + \theta \Delta t \, a(u', v) = \langle u, v \rangle - (1 - \theta)
  \Delta t \, a(u, v) + \Delta t \big(\theta \ell_1(v) + (1 - \theta) \ell_0(v)\big).$$

In this form, the step is a Galerkin problem for the form $\langle \cdot, \cdot \rangle + \theta
\Delta t \, a$. -/
theorem iff_forall_inner_add (hΔt : Δt ≠ 0) :
    IsThetaStep a θ Δt ℓ₀ ℓ₁ u u' ↔ ∀ v, ⟪u', v⟫ + θ * Δt * a u' v
      = ⟪u, v⟫ - (1 - θ) * Δt * a u v + Δt * (θ * ℓ₁ v + (1 - θ) * ℓ₀ v) := by
  have e : ∀ v, ⟪Δt⁻¹ • (u' - u), v⟫ + a (θ • u' + (1 - θ) • u) v
      - (θ * ℓ₁ v + (1 - θ) * ℓ₀ v)
      = Δt⁻¹ * ((⟪u', v⟫ + θ * Δt * a u' v)
        - (⟪u, v⟫ - (1 - θ) * Δt * a u v + Δt * (θ * ℓ₁ v + (1 - θ) * ℓ₀ v))) := by
    intro v
    simp only [real_inner_smul_left, inner_sub_left, map_add, map_smul, add_apply, smul_apply,
      smul_eq_mul]
    field_simp
    ring
  refine forall_congr' fun v => ?_
  rw [← sub_eq_zero, e v, mul_eq_zero, or_iff_right (inv_ne_zero hΔt), sub_eq_zero]

/-- Let $u'$ be the θ-step of $u$ and let $\Delta t \neq 0$. Then for every $v \in K$, $\langle u',
v \rangle + \theta \Delta t \, a(u', v) = \langle u, v \rangle - (1 - \theta) \Delta t \, a(u,
v) + \Delta t (\theta \ell_1(v) + (1 - \theta) \ell_0(v))$. -/
theorem inner_add_eq (h : IsThetaStep a θ Δt ℓ₀ ℓ₁ u u') (hΔt : Δt ≠ 0) (v : K) :
    ⟪u', v⟫ + θ * Δt * a u' v
      = ⟪u, v⟫ - (1 - θ) * Δt * a u v + Δt * (θ * ℓ₁ v + (1 - θ) * ℓ₀ v) :=
  (iff_forall_inner_add hΔt).1 h v

/-- **Existence and uniqueness of the θ-step** ([quarteroni2000numerical], §13.3, the remark that
the system (13.16) has exactly one solution). Let $K$ be a real Hilbert space, let
$\theta \ge 0$ and $\Delta t > 0$, and let $a(v, v) \ge 0$ for all $v$. Then for all bounded
functionals $\ell_0, \ell_1$ and every $u \in K$, there is exactly one θ-step $u'$ of $u$.

The form $\langle \cdot, \cdot \rangle + \theta \Delta t \, a$ is coercive with constant $1$,
and `SesqForm.laxMilgram` solves the step in the form of
`Variational.IsThetaStep.iff_forall_inner_add`. -/
theorem existsUnique [CompleteSpace K] (hθ : 0 ≤ θ) (hΔt : 0 < Δt) (hpos : a.IsCoerciveWith 0)
    (ℓ₀ ℓ₁ : K →L[ℝ] ℝ) (u : K) : ∃! u', IsThetaStep a θ Δt ℓ₀ ℓ₁ u u' := by
  set b : SesqForm ℝ K := innerSL ℝ + (θ * Δt) • a with hb
  set ℓ : K →L[ℝ] ℝ := innerSL ℝ u - ((1 - θ) * Δt) • a u + Δt • (θ • ℓ₁ + (1 - θ) • ℓ₀)
    with hℓ
  have hbc : b.IsCoerciveWith 1 := fun v => by
    have h0 := hpos v
    simp only [zero_mul, RCLike.re_to_real] at h0
    simp only [hb, add_apply, smul_apply, innerSL_apply_apply, real_inner_self_eq_norm_sq,
      smul_eq_mul, RCLike.re_to_real, one_mul]
    nlinarith [mul_nonneg hθ hΔt.le]
  have key := b.laxMilgram ℓ one_pos hbc
  simp_rw [iff_forall_inner_add hΔt.ne']
  convert key using 3 with u' v
  simp only [hb, hℓ, add_apply, smul_apply, sub_apply, innerSL_apply_apply, smul_eq_mul]

end IsThetaStep

/-- In a real inner product space, $\frac12 (\|u\|^2 - \|v\|^2) \le \langle u - v, u \rangle$ for
all $u$ and $v$.

The proof is $\langle u - v, u \rangle = \|u\|^2 - \langle v, u \rangle \ge \|u\|^2 - \|u\|
\|v\| \ge \|u\|^2 - \frac12 (\|u\|^2 + \|v\|^2)$, the hint of Exercise 13.3 of
[quarteroni2000numerical]. It is the one inequality behind every energy estimate of backward
Euler. -/
theorem half_norm_sq_sub_le_inner_sub (u v : K) :
    (1 / 2 : ℝ) * (‖u‖ ^ 2 - ‖v‖ ^ 2) ≤ ⟪u - v, u⟫ := by
  rw [inner_sub_left, real_inner_self_eq_norm_sq]
  have h1 := real_inner_le_norm v u
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

namespace IsThetaStep

variable {a : SesqForm ℝ K} {θ Δt : ℝ} {ℓ₀ ℓ₁ : K →L[ℝ] ℝ} {u u' : K}

/-- **The energy identity of the θ-method.** Let $u'$ be the θ-step of $u$ without sources
($\ell_0 = \ell_1 = 0$), let $\Delta t \neq 0$, and let $w = \theta u' + (1 - \theta) u$. Then
$$\tfrac12 \big(\|u'\|^2 - \|u\|^2\big) = -\Delta t \, a(w, w) - \big(\theta - \tfrac12\big)
  \|u' - u\|^2.$$

The proof tests the step with $v = w$ and writes $w = \frac12 (u' + u) + (\theta - \frac12)(u' -
u)$, so that $\langle u' - u, w \rangle = \frac12 (\|u'\|^2 - \|u\|^2) + (\theta - \frac12)
\|u' - u\|^2$. No symmetry or positivity of $a$ is used. -/
theorem energy_identity (h : IsThetaStep a θ Δt 0 0 u u') (hΔt : Δt ≠ 0) :
    (1 / 2 : ℝ) * (‖u'‖ ^ 2 - ‖u‖ ^ 2)
      = -(Δt * a (θ • u' + (1 - θ) • u) (θ • u' + (1 - θ) • u))
        - (θ - 1 / 2) * ‖u' - u‖ ^ 2 := by
  set w := θ • u' + (1 - θ) • u with hw
  have h1 := h w
  simp only [zero_apply, mul_zero, add_zero, real_inner_smul_left] at h1
  have h2 : ⟪u' - u, w⟫ = -(Δt * a w w) := by
    field_simp at h1
    linear_combination h1
  have h3 : ⟪u' - u, w⟫ = (1 / 2 : ℝ) * (‖u'‖ ^ 2 - ‖u‖ ^ 2) + (θ - 1 / 2) * ‖u' - u‖ ^ 2 := by
    have hw' : w = (1 / 2 : ℝ) • (u' + u) + (θ - 1 / 2) • (u' - u) := by
      rw [hw]; module
    rw [hw', inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, inner_sub_left, inner_add_right, inner_add_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm u u']
    ring
  linarith

/-- **Unconditional stability of the θ-method for $\theta \ge \frac12$** ([quarteroni2000numerical],
§13.3.1, first conclusion). Let $u'$ be the θ-step of $u$ without sources, with
$\theta \ge \frac12$ and $\Delta t > 0$, and let $a(v, v) \ge 0$ for all $v$. Then
$\|u'\| \le \|u\|$.

Both terms on the right of `Variational.IsThetaStep.energy_identity` are at most $0$. No
symmetry of $a$ is needed, so this covers the nonsymmetric transport forms of §13.10. -/
theorem norm_le_of_half_le (h : IsThetaStep a θ Δt 0 0 u u') (hθ : 1 / 2 ≤ θ) (hΔt : 0 < Δt)
    (hpos : a.IsCoerciveWith 0) : ‖u'‖ ≤ ‖u‖ := by
  have hid := h.energy_identity hΔt.ne'
  have h0 := hpos (θ • u' + (1 - θ) • u)
  simp only [zero_mul, RCLike.re_to_real] at h0
  have : ‖u'‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    nlinarith [mul_nonneg hΔt.le h0, mul_nonneg (sub_nonneg.2 hθ) (sq_nonneg ‖u' - u‖)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

/-- **The energy inequality of backward Euler** ([quarteroni2000numerical], (13.19)). Let $u'$ be
the backward Euler step ($\theta = 1$) of $u$ without sources, with $\Delta t > 0$. Then
$$\|u'\|^2 + 2 \Delta t \, a(u', u') \le \|u\|^2.$$

The proof tests with $v = u'$ and uses `Variational.half_norm_sq_sub_le_inner_sub`. No
positivity of $a$ is used. -/
theorem norm_sq_add_two_mul_le (h : IsThetaStep a 1 Δt 0 0 u u') (hΔt : 0 < Δt) :
    ‖u'‖ ^ 2 + 2 * Δt * a u' u' ≤ ‖u‖ ^ 2 := by
  have h1 := h.inner_add_eq hΔt.ne' u'
  simp only [zero_apply, sub_self, zero_mul, mul_zero, add_zero, one_mul, sub_zero] at h1
  have h2 := half_norm_sq_sub_le_inner_sub u' u
  rw [inner_sub_left] at h2
  linarith

/-- Let $u'$ be the backward Euler step of $u$ with sources $\ell_0, \ell_1$, and let
$\Delta t > 0$. Then $\|u'\|^2 + 2 \Delta t \, a(u', u') \le \|u\|^2 + 2 \Delta t \,
\ell_1(u')$. -/
theorem norm_sq_add_two_mul_le_add (h : IsThetaStep a 1 Δt ℓ₀ ℓ₁ u u') (hΔt : 0 < Δt) :
    ‖u'‖ ^ 2 + 2 * Δt * a u' u' ≤ ‖u‖ ^ 2 + 2 * Δt * ℓ₁ u' := by
  have h1 := h.inner_add_eq hΔt.ne' u'
  simp only [sub_self, zero_mul, add_zero, one_mul, sub_zero] at h1
  have h2 := half_norm_sq_sub_le_inner_sub u' u
  rw [inner_sub_left] at h2
  linarith

/-- **The telescoped estimate of backward Euler** ([quarteroni2000numerical], (13.20)). Let
$\Delta t > 0$, and let $u_{k+1}$ be the backward Euler step of $u_k$ without sources for every
$k < n$. Then
$$\|u_n\|^2 + 2 \Delta t \sum_{k < n} a(u_{k+1}, u_{k+1}) \le \|u_0\|^2.$$

The proof is induction on `Variational.IsThetaStep.norm_sq_add_two_mul_le`. -/
theorem norm_sq_add_sum_le {u : ℕ → K} {n : ℕ} (hΔt : 0 < Δt)
    (h : ∀ k < n, IsThetaStep a 1 Δt 0 0 (u k) (u (k + 1))) :
    ‖u n‖ ^ 2 + 2 * Δt * ∑ k ∈ Finset.range n, a (u (k + 1)) (u (k + 1)) ≤ ‖u 0‖ ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih fun k hk => h k (Nat.lt_succ_of_lt hk)
    have hn := (h n (Nat.lt_succ_self n)).norm_sq_add_two_mul_le hΔt
    rw [Finset.sum_range_succ, mul_add]
    linarith

/-- Let $u'$ be the backward Euler step of $u$ with sources $\ell_0, \ell_1$, let $\Delta t > 0$,
and let $\alpha \|v\|^2 \le a(v, v)$ for all $v$ with a constant $\alpha > 0$. Then
$$\|u'\|^2 + \Delta t \, a(u', u') \le \|u\|^2 + \alpha^{-1} \Delta t \, \|\ell_1\|^2.$$

The proof combines $2 \Delta t \, \ell_1(u') \le \Delta t (\|\ell_1\|^2 / \alpha + \alpha
\|u'\|^2)$ and $\alpha \|u'\|^2 \le a(u', u')$. -/
theorem norm_sq_add_mul_le_of_coercive (h : IsThetaStep a 1 Δt ℓ₀ ℓ₁ u u') (hΔt : 0 < Δt)
    {α : ℝ} (hα : 0 < α) (hcoer : a.IsCoerciveWith α) :
    ‖u'‖ ^ 2 + Δt * a u' u' ≤ ‖u‖ ^ 2 + α⁻¹ * (Δt * ‖ℓ₁‖ ^ 2) := by
  have h1 := h.norm_sq_add_two_mul_le_add hΔt
  have h2 : ℓ₁ u' ≤ ‖ℓ₁‖ * ‖u'‖ := (le_abs_self _).trans (ℓ₁.le_opNorm u')
  have h3 : 2 * ‖ℓ₁‖ * ‖u'‖ ≤ α * ‖u'‖ ^ 2 + ‖ℓ₁‖ ^ 2 / α :=
    IsSemidiscreteGalerkin.two_mul_mul_norm_le hα ‖ℓ₁‖ u'
  have h4 : α * ‖u'‖ ^ 2 ≤ a u' u' := hcoer u'
  have h5 : α⁻¹ * (Δt * ‖ℓ₁‖ ^ 2) = Δt * (‖ℓ₁‖ ^ 2 / α) := by ring
  rw [h5]
  nlinarith [mul_le_mul_of_nonneg_left h3 hΔt.le, mul_le_mul_of_nonneg_left h2 hΔt.le]

/-- **The estimate of backward Euler with sources under coercivity** ([quarteroni2000numerical],
(13.21), Remark 13.1 and Exercise 13.4). Let $\alpha \|v\|^2 \le a(v, v)$ for all $v$ with a
constant $\alpha > 0$, let $\Delta t > 0$, and let $u_{k+1}$ be the backward Euler step of $u_k$
with sources $\ell_k, \ell_{k+1}$ for every $k < n$. Then
$$\|u_n\|^2 + \Delta t \sum_{k < n} a(u_{k+1}, u_{k+1}) \le \|u_0\|^2 + \alpha^{-1} \sum_{k < n}
  \Delta t \, \|\ell_{k+1}\|^2.$$

The constant $C(n)$ of the book is here $\max\{1, \alpha^{-1}\}$, independent of $n$, at the
price of half the coefficient of the terms of the form. -/
theorem norm_sq_add_sum_le_of_coercive {u : ℕ → K} {ℓ : ℕ → K →L[ℝ] ℝ} {n : ℕ} (hΔt : 0 < Δt)
    {α : ℝ} (hα : 0 < α) (hcoer : a.IsCoerciveWith α)
    (h : ∀ k < n, IsThetaStep a 1 Δt (ℓ k) (ℓ (k + 1)) (u k) (u (k + 1))) :
    ‖u n‖ ^ 2 + Δt * ∑ k ∈ Finset.range n, a (u (k + 1)) (u (k + 1))
      ≤ ‖u 0‖ ^ 2 + α⁻¹ * ∑ k ∈ Finset.range n, Δt * ‖ℓ (k + 1)‖ ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih fun k hk => h k (Nat.lt_succ_of_lt hk)
    have hn := (h n (Nat.lt_succ_self n)).norm_sq_add_mul_le_of_coercive hΔt hα hcoer
    rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add, mul_add]
    linarith

/-- Let $u'$ be the backward Euler step of $u$ with sources $\ell_0, \ell_1$, let
$0 < \Delta t \le \frac12$, and let $a(v, v) \ge 0$ for all $v$. Then
$$\|u'\|^2 + 2 \Delta t \, a(u', u') \le (1 - \Delta t)^{-1} \big(\|u\|^2 + \Delta t \,
  \|\ell_1\|^2\big).$$

The proof uses $2 \Delta t \, \ell_1(u') \le \Delta t (\|\ell_1\|^2 + \|u'\|^2)$. -/
theorem norm_sq_add_two_mul_le_of_le (h : IsThetaStep a 1 Δt ℓ₀ ℓ₁ u u') (hΔt : 0 < Δt)
    (hΔt' : Δt ≤ 1 / 2) (hpos : a.IsCoerciveWith 0) :
    ‖u'‖ ^ 2 + 2 * Δt * a u' u' ≤ (1 - Δt)⁻¹ * (‖u‖ ^ 2 + Δt * ‖ℓ₁‖ ^ 2) := by
  have h1 := h.norm_sq_add_two_mul_le_add hΔt
  have h2 : ℓ₁ u' ≤ ‖ℓ₁‖ * ‖u'‖ := (le_abs_self _).trans (ℓ₁.le_opNorm u')
  have h3 : 2 * ‖ℓ₁‖ * ‖u'‖ ≤ 1 * ‖u'‖ ^ 2 + ‖ℓ₁‖ ^ 2 / 1 :=
    IsSemidiscreteGalerkin.two_mul_mul_norm_le one_pos ‖ℓ₁‖ u'
  have h4 := hpos u'
  simp only [zero_mul, RCLike.re_to_real] at h4
  have hpos1 : 0 < 1 - Δt := by linarith
  have h5 : (1 - Δt) * ‖u'‖ ^ 2 + 2 * Δt * a u' u' ≤ ‖u‖ ^ 2 + Δt * ‖ℓ₁‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left h3 hΔt.le, mul_le_mul_of_nonneg_left h2 hΔt.le]
  rw [← div_eq_inv_mul, le_div_iff₀ hpos1]
  nlinarith [mul_nonneg (mul_nonneg two_pos.le hΔt.le) h4]

/-- **The estimate of backward Euler with sources without coercivity** ([quarteroni2000numerical],
(13.21) as printed, with a constant $C(n)$ that depends on $n$). Let $0 < \Delta t \le \frac12$,
let $a(v, v) \ge 0$ for all $v$, and let $u_{k+1}$ be the backward Euler step of $u_k$ with
sources $\ell_k, \ell_{k+1}$ for every $k < n$. Then
$$\|u_n\|^2 + 2 \Delta t \sum_{k < n} a(u_{k+1}, u_{k+1}) \le (1 - \Delta t)^{-n}
  \Big(\|u_0\|^2 + \sum_{k < n} \Delta t \, \|\ell_{k+1}\|^2\Big).$$

This is a discrete Gronwall inequality in its simplest form.
`Variational.IsThetaStep.inv_one_sub_pow_le_exp` bounds the constant by $e^{2 n \Delta t}$. -/
theorem norm_sq_add_sum_le_of_le {u : ℕ → K} {ℓ : ℕ → K →L[ℝ] ℝ} {n : ℕ} (hΔt : 0 < Δt)
    (hΔt' : Δt ≤ 1 / 2) (hpos : a.IsCoerciveWith 0)
    (h : ∀ k < n, IsThetaStep a 1 Δt (ℓ k) (ℓ (k + 1)) (u k) (u (k + 1))) :
    ‖u n‖ ^ 2 + 2 * Δt * ∑ k ∈ Finset.range n, a (u (k + 1)) (u (k + 1))
      ≤ (1 - Δt)⁻¹ ^ n * (‖u 0‖ ^ 2 + ∑ k ∈ Finset.range n, Δt * ‖ℓ (k + 1)‖ ^ 2) := by
  have hpos1 : 0 < 1 - Δt := by linarith
  have hinv : 1 ≤ (1 - Δt)⁻¹ := one_le_inv₀ hpos1 |>.2 (by linarith)
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih fun k hk => h k (Nat.lt_succ_of_lt hk)
    have hn := (h n (Nat.lt_succ_self n)).norm_sq_add_two_mul_le_of_le hΔt hΔt' hpos
    have hsum : 0 ≤ ∑ k ∈ Finset.range n, a (u (k + 1)) (u (k + 1)) :=
      Finset.sum_nonneg fun k _ => by simpa using hpos (u (k + 1))
    have hpown : 1 ≤ (1 - Δt)⁻¹ ^ n := one_le_pow₀ hinv
    have hℓn : 0 ≤ Δt * ‖ℓ (n + 1)‖ ^ 2 := by positivity
    calc ‖u (n + 1)‖ ^ 2 + 2 * Δt * ∑ k ∈ Finset.range (n + 1), a (u (k + 1)) (u (k + 1))
        = ‖u (n + 1)‖ ^ 2 + 2 * Δt * a (u (n + 1)) (u (n + 1))
          + 2 * Δt * ∑ k ∈ Finset.range n, a (u (k + 1)) (u (k + 1)) := by
          rw [Finset.sum_range_succ]; ring
      _ ≤ (1 - Δt)⁻¹ * (‖u n‖ ^ 2 + 2 * Δt * ∑ k ∈ Finset.range n, a (u (k + 1)) (u (k + 1))
          + Δt * ‖ℓ (n + 1)‖ ^ 2) := by
          nlinarith [mul_nonneg (mul_nonneg two_pos.le hΔt.le) hsum]
      _ ≤ (1 - Δt)⁻¹ * ((1 - Δt)⁻¹ ^ n * (‖u 0‖ ^ 2 + ∑ k ∈ Finset.range n, Δt * ‖ℓ (k + 1)‖ ^ 2)
          + Δt * ‖ℓ (n + 1)‖ ^ 2) := by gcongr
      _ ≤ (1 - Δt)⁻¹ ^ (n + 1)
          * (‖u 0‖ ^ 2 + ∑ k ∈ Finset.range (n + 1), Δt * ‖ℓ (k + 1)‖ ^ 2) := by
          rw [Finset.sum_range_succ, pow_succ' (1 - Δt)⁻¹ n, mul_assoc]
          gcongr
          nlinarith

/-- Let $0 \le \Delta t \le \frac12$ and $n \in \mathbb{N}$. Then
$(1 - \Delta t)^{-n} \le e^{2 n \Delta t}$.

So the constant of `Variational.IsThetaStep.norm_sq_add_sum_le_of_le` is at most $e^{2 t_n}$ at
the time $t_n = n \Delta t$. -/
theorem inv_one_sub_pow_le_exp {Δt : ℝ} (hΔt : 0 ≤ Δt) (hΔt' : Δt ≤ 1 / 2) (n : ℕ) :
    (1 - Δt)⁻¹ ^ n ≤ exp (2 * n * Δt) := by
  have hpos1 : 0 < 1 - Δt := by linarith
  have h1 : (1 - Δt)⁻¹ ≤ 1 + 2 * Δt := by
    rw [inv_le_iff_one_le_mul₀ hpos1]
    nlinarith
  have h2 : 1 + 2 * Δt ≤ exp (2 * Δt) := by
    have := add_one_le_exp (2 * Δt)
    linarith
  calc (1 - Δt)⁻¹ ^ n ≤ exp (2 * Δt) ^ n :=
        pow_le_pow_left₀ (inv_nonneg.2 hpos1.le) (h1.trans h2) n
    _ = exp (2 * n * Δt) := by rw [← exp_nat_mul]; ring_nf

end IsThetaStep

/-! ### Eigenpairs of a form -/

/-- **Eigenpairs of a bilinear form** relative to the inner product ([quarteroni2000numerical],
Definition 13.1, and its discrete form (13.22) on $V_h$). A pair $(\lambda, w)$ with
$\lambda \in \mathbb{R}$ and $w \in K$ is an eigenpair of $a$ if $w \neq 0$ and
$a(w, v) = \lambda \langle w, v \rangle$ for every $v \in K$. -/
def IsFormEigenpair (a : SesqForm ℝ K) (lam : ℝ) (w : K) : Prop :=
  w ≠ 0 ∧ ∀ v, a w v = lam * ⟪w, v⟫

/-- On a real Hilbert space $K$, a pair $(\lambda, w)$ is an eigenpair of the form $a$ if and only
if $w$ is an eigenvector with eigenvalue $\lambda$ of the operator $A$ of $a$, which satisfies
$\langle Au, v \rangle = a(u, v)$. -/
theorem isFormEigenpair_iff_hasEigenvector [CompleteSpace K] (a : SesqForm ℝ K) (lam : ℝ)
    (w : K) :
    IsFormEigenpair a lam w ↔
      Module.End.HasEigenvector (SesqForm.toOperator a : K →ₗ[ℝ] K) lam w := by
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, IsFormEigenpair, and_comm]
  refine and_congr_left fun _ => ?_
  simp only [ContinuousLinearMap.coe_coe]
  constructor
  · intro h
    exact ext_inner_right ℝ fun v => by
      rw [SesqForm.inner_toOperator, h v, real_inner_smul_left]
  · intro h v
    rw [← SesqForm.inner_toOperator, h, real_inner_smul_left]

namespace IsFormEigenpair

variable {a : SesqForm ℝ K} {lam : ℝ} {w : K}

/-- If $(\lambda, w)$ is an eigenpair of $a$, then $a(w, w) = \lambda \|w\|^2$. -/
theorem apply_self (h : IsFormEigenpair a lam w) : a w w = lam * ‖w‖ ^ 2 := by
  rw [h.2 w, real_inner_self_eq_norm_sq]

/-- If $a$ is coercive with constant $c$, that is, $c \|v\|^2 \le a(v, v)$ for all $v$, then every
eigenvalue $\lambda$ of $a$ satisfies $c \le \lambda$. -/
theorem le_of_coercive {c : ℝ} (hcoer : a.IsCoerciveWith c) (h : IsFormEigenpair a lam w) :
    c ≤ lam := by
  have h1 := hcoer w
  rw [RCLike.re_to_real, h.apply_self] at h1
  exact le_of_mul_le_mul_right h1 (pow_pos (norm_pos_iff.2 h.1) 2)

/-- If $a$ is coercive with a constant $c > 0$, then every eigenvalue of $a$ is positive
([quarteroni2000numerical], §13.3.1). -/
theorem pos_of_coercive {c : ℝ} (hc : 0 < c) (hcoer : a.IsCoerciveWith c)
    (h : IsFormEigenpair a lam w) : 0 < lam :=
  hc.trans_le (h.le_of_coercive hcoer)

/-- If $a(v, v) \le \lambda_{\max} \|v\|^2$ for all $v$, then every eigenvalue $\lambda$ of $a$
satisfies $\lambda \le \lambda_{\max}$. -/
theorem le_of_le {lmax : ℝ} (hle : ∀ v, a v v ≤ lmax * ‖v‖ ^ 2) (h : IsFormEigenpair a lam w) :
    lam ≤ lmax := by
  have h1 := hle w
  rw [h.apply_self] at h1
  exact le_of_mul_le_mul_right h1 (pow_pos (norm_pos_iff.2 h.1) 2)

end IsFormEigenpair

/-- **The orthonormal eigenbasis of a symmetric form** ([quarteroni2000numerical], §13.3.1, where
the eigenvectors of a symmetric coercive form on $V_h$ form an $L^2$-orthonormal basis). Let $K$
be a finite-dimensional real inner product space of dimension $N$, and let $a$ be a symmetric
form on $K$. Then there are $\lambda_1, \dots, \lambda_N \in \mathbb{R}$ and an orthonormal
basis $b_1, \dots, b_N$ of $K$ such that $(\lambda_i, b_i)$ is an eigenpair of $a$ for every
$i$.

Coercivity is not needed. The proof is the spectral theorem
`LinearMap.IsSymmetric.eigenvectorBasis` for the operator of the form, which is symmetric by
`SesqForm.isHermitian_iff_toOperator_isSymmetric`. The indices run over
`Fin (Module.finrank ℝ K)`. -/
theorem exists_orthonormalBasis_isFormEigenpair [FiniteDimensional ℝ K] {a : SesqForm ℝ K}
    (ha : a.IsHermitian) :
    ∃ (lam : Fin (Module.finrank ℝ K) → ℝ) (b : OrthonormalBasis (Fin (Module.finrank ℝ K)) ℝ K),
      ∀ i, IsFormEigenpair a (lam i) (b i) := by
  have : CompleteSpace K := FiniteDimensional.complete ℝ K
  have hsymm := (SesqForm.isHermitian_iff_toOperator_isSymmetric a).1 ha
  refine ⟨hsymm.eigenvalues rfl, hsymm.eigenvectorBasis rfl, fun i => ?_⟩
  rw [isFormEigenpair_iff_hasEigenvector]
  exact hsymm.hasEigenvector_eigenvectorBasis rfl i

/-- **The generalized eigenvalue problem in coordinates** ([quarteroni2000numerical], (13.22),
$A_{fe} w = \lambda_h M w$). Let $\varphi$ be a finite basis of $K$, let $A$ be the stiffness
matrix $A_{ij} = a(\varphi_j, \varphi_i)$, and let $M$ be the mass matrix
$M_{ij} = \langle \varphi_j, \varphi_i \rangle$. Then for $\lambda \in \mathbb{R}$ and
$\xi \in \mathbb{R}^\iota$, the pair $(\lambda, \sum_j \xi_j \varphi_j)$ is an eigenpair of $a$
if and only if $\xi \neq 0$ and $A \xi = \lambda M \xi$.

The stiffness matrix is `SesqForm.gramMatrix a φ`, and the mass matrix is
`SesqForm.gramMatrix (innerSL ℝ) φ`. -/
theorem isFormEigenpair_iff_gramMatrix_mulVec {ι : Type*} [Fintype ι] (a : SesqForm ℝ K)
    (φ : Module.Basis ι ℝ K) (lam : ℝ) (ξ : ι → ℝ) :
    IsFormEigenpair a lam (∑ j, ξ j • φ j) ↔
      ξ ≠ 0 ∧ a.gramMatrix φ *ᵥ ξ = lam • SesqForm.gramMatrix (innerSL ℝ) φ *ᵥ ξ := by
  have hexp : ∀ (b : SesqForm ℝ K) (v : K), b (∑ j, ξ j • φ j) v = ∑ j, ξ j * b (φ j) v := by
    intro b v
    simp [map_sum, smul_eq_mul]
  have hmul : ∀ (b : SesqForm ℝ K) (i : ι), (b.gramMatrix φ *ᵥ ξ) i = b (∑ j, ξ j • φ j) (φ i) := by
    intro b i
    rw [hexp, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  refine and_congr ?_ ?_
  · rw [not_iff_not]
    constructor
    · intro h
      exact funext fun i => Fintype.linearIndependent_iff.1 φ.linearIndependent ξ h i
    · rintro rfl
      simp
  · constructor
    · intro h
      ext i
      rw [Pi.smul_apply, hmul, hmul, h (φ i), smul_eq_mul, innerSL_apply_apply]
    · intro h v
      have key : (a (∑ j, ξ j • φ j) : K →ₗ[ℝ] ℝ)
          = ((lam • innerSL ℝ (∑ j, ξ j • φ j) : K →L[ℝ] ℝ) : K →ₗ[ℝ] ℝ) := by
        refine φ.ext fun i => ?_
        have := congrFun h i
        rw [Pi.smul_apply, hmul, hmul, smul_eq_mul, innerSL_apply_apply] at this
        simp only [ContinuousLinearMap.coe_coe, smul_apply, innerSL_apply_apply, smul_eq_mul]
        exact this
      have := LinearMap.congr_fun key v
      simp only [ContinuousLinearMap.coe_coe, smul_apply, innerSL_apply_apply, smul_eq_mul] at this
      exact this

namespace IsThetaStep

variable {a : SesqForm ℝ K} {θ Δt : ℝ} {u u' : K}

/-- **The θ-method in an eigenvector direction** ([quarteroni2000numerical], §13.3.1, the recursion
$u_i^{k+1} = u_i^k [1 - (1 - \theta) \lambda_h^i \Delta t] / [1 + \theta \lambda_h^i \Delta
t]$). Let $a$ be symmetric, let $(\lambda, w)$ be an eigenpair of $a$, let $u'$ be the θ-step of
$u$ without sources, and let $\Delta t \neq 0$ and $1 + \theta \lambda \Delta t \neq 0$. Then
$$\langle u', w \rangle = r_\theta(\lambda \Delta t) \, \langle u, w \rangle, \qquad
  r_\theta(x) = \frac{1 - (1 - \theta) x}{1 + \theta x}.$$
-/
theorem inner_eq_of_isFormEigenpair (h : IsThetaStep a θ Δt 0 0 u u') (ha : a.IsHermitian)
    {lam : ℝ} {w : K} (hw : IsFormEigenpair a lam w) (hΔt : Δt ≠ 0)
    (hden : 1 + θ * lam * Δt ≠ 0) :
    ⟪u', w⟫ = (1 - (1 - θ) * lam * Δt) / (1 + θ * lam * Δt) * ⟪u, w⟫ := by
  have h1 := h.inner_add_eq hΔt w
  have e : ∀ x, a x w = lam * ⟪x, w⟫ := fun x => by
    rw [ha x w, hw.2 x, real_inner_comm, RCLike.conj_to_real]
  simp only [e, zero_apply, mul_zero, add_zero] at h1
  rw [div_mul_eq_mul_div, eq_div_iff hden]
  linear_combination h1

/-- **Conditional stability of the θ-method, the sufficient condition** ([quarteroni2000numerical],
§13.3.1, $\Delta t \le 2 / ((1 - 2\theta) \lambda_h^{N_h})$). Let $K$ be a real Hilbert space,
let $a$ be symmetric with $0 \le a(v, v) \le \lambda_{\max} \|v\|^2$ for all $v$, let
$\Delta t > 0$ with $(1 - 2\theta) \lambda_{\max} \Delta t \le 2$, and let $u'$ be the θ-step of
$u$ without sources. Then $\|u'\| \le \|u\|$.

The proof uses no eigenvectors. By `Variational.IsThetaStep.energy_identity`, it suffices that
$(\frac12 - \theta) \|u' - u\|^2 \le \Delta t \, a(w, w)$. The step gives
$u' - u = -\Delta t \, Bw$ for the operator $B$ of the form, and the operator Cauchy–Schwarz
inequality `LinearMap.IsSymmetricBoundedBy.norm_apply_sq_le` gives $\|Bw\|^2 \le \lambda_{\max}
\langle Bw, w \rangle = \lambda_{\max} a(w, w)$. The hypothesis $\theta < \frac12$ of the book
is not needed: for $\theta \ge \frac12$ the condition holds trivially, and so does the
conclusion. `Numlib.FiniteDifference.Parabolic` uses this form in the inner product of the mass
matrix. -/
theorem norm_le_of_le_of_lt_half [CompleteSpace K] (h : IsThetaStep a θ Δt 0 0 u u')
    (ha : a.IsHermitian) (hpos : a.IsCoerciveWith 0) {lmax : ℝ}
    (hle : ∀ v, a v v ≤ lmax * ‖v‖ ^ 2) (hΔt : 0 < Δt)
    (hcfl : (1 - 2 * θ) * lmax * Δt ≤ 2) : ‖u'‖ ≤ ‖u‖ := by
  set B : K →ₗ[ℝ] K := (SesqForm.toOperator a : K →ₗ[ℝ] K) with hB
  have hBs : B.IsSymmetricBoundedBy 0 lmax := by
    refine ⟨(SesqForm.isHermitian_iff_toOperator_isSymmetric a).1 ha, fun x => ?_, fun x => ?_⟩
    · simpa [hB, SesqForm.inner_toOperator] using hpos x
    · simpa [hB, SesqForm.inner_toOperator] using hle x
  set w := θ • u' + (1 - θ) • u with hw
  have hstep : u' - u = -(Δt • B w) := by
    have : Δt⁻¹ • (u' - u) = -(B w) := by
      refine ext_inner_right ℝ fun v => ?_
      rw [inner_neg_left, hB, ContinuousLinearMap.coe_coe, SesqForm.inner_toOperator]
      have := h v
      simp only [zero_apply, mul_zero, add_zero] at this
      rw [← hw] at this
      linarith
    calc u' - u = Δt • (Δt⁻¹ • (u' - u)) := by rw [smul_smul, mul_inv_cancel₀ hΔt.ne', one_smul]
      _ = -(Δt • B w) := by rw [this, smul_neg]
  have hnorm : ‖u' - u‖ ^ 2 ≤ Δt ^ 2 * (lmax * a w w) := by
    rw [hstep, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hΔt, mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    have := hBs.norm_apply_sq_le le_rfl w
    rwa [RCLike.re_to_real, hB, ContinuousLinearMap.coe_coe, SesqForm.inner_toOperator] at this
  have hid := h.energy_identity hΔt.ne'
  rw [← hw] at hid
  have h0 : 0 ≤ a w w := by simpa using hpos w
  have hkey : (1 / 2 - θ) * ‖u' - u‖ ^ 2 ≤ Δt * a w w := by
    rcases le_or_gt (1 / 2) θ with hθ | hθ
    · nlinarith [mul_nonneg hΔt.le h0, sq_nonneg ‖u' - u‖]
    · calc (1 / 2 - θ) * ‖u' - u‖ ^ 2 ≤ (1 / 2 - θ) * (Δt ^ 2 * (lmax * a w w)) :=
            mul_le_mul_of_nonneg_left hnorm (by linarith)
        _ = Δt * a w w * ((1 - 2 * θ) * lmax * Δt / 2) := by ring
        _ ≤ Δt * a w w * 1 :=
            mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hΔt.le h0)
        _ = Δt * a w w := mul_one _
  have : ‖u'‖ ^ 2 ≤ ‖u‖ ^ 2 := by linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

/-- **The θ-step of an eigenvector.** Let $(\lambda, w)$ be an eigenpair of $a$, and let
$\Delta t \neq 0$ and $1 + \theta \lambda \Delta t \neq 0$. Then
$r_\theta(\lambda \Delta t) \, w$ is the θ-step of $w$ without sources, where $r_\theta(x) =
(1 - (1 - \theta) x) / (1 + \theta x)$. -/
theorem smul_of_isFormEigenpair {lam : ℝ} {w : K} (hw : IsFormEigenpair a lam w)
    (hΔt : Δt ≠ 0) (hden : 1 + θ * lam * Δt ≠ 0) :
    IsThetaStep a θ Δt 0 0 w (((1 - (1 - θ) * lam * Δt) / (1 + θ * lam * Δt)) • w) := by
  intro v
  set r := (1 - (1 - θ) * lam * Δt) / (1 + θ * lam * Δt) with hr
  have hr' : r * (1 + θ * lam * Δt) = 1 - (1 - θ) * lam * Δt := by
    rw [hr, div_mul_cancel₀ _ hden]
  have e : θ • (r • w) + (1 - θ) • w = (θ * r + (1 - θ)) • w := by
    rw [smul_smul, add_smul]
  rw [e, map_smulₛₗ, smul_apply, hw.2, RCLike.conj_to_real, smul_eq_mul, real_inner_smul_left,
    inner_sub_left, real_inner_smul_left, zero_apply, mul_zero, mul_zero, add_zero]
  have : Δt⁻¹ * (r - 1) = -(lam * (θ * r + (1 - θ))) := by
    field_simp
    linear_combination hr'
  linear_combination ⟪w, v⟫ * this

/-- **Conditional stability of the θ-method, the sharp condition** ([quarteroni2000numerical],
§13.3.1). Let $K$ be a real Hilbert space, let $a$ be symmetric and coercive with a constant
$c > 0$, let $\theta \ge 0$ and $\Delta t > 0$. Let $(\lambda_{\max}, w_0)$ be an eigenpair of
$a$ with $a(v, v) \le \lambda_{\max} \|v\|^2$ for all $v$. Then the θ-step without sources
satisfies $\|u'\| \le \|u\|$ for every $u$ and every θ-step $u'$ of $u$ if and only if
$$(1 - 2\theta) \lambda_{\max} \Delta t \le 2.$$

Necessity: the step multiplies the eigenvector $w_0$ by $r_\theta(\lambda_{\max} \Delta t)$,
whose absolute value is at most $1$ if and only if the condition holds. Sufficiency is
`Variational.IsThetaStep.norm_le_of_le_of_lt_half`. For $\theta \ge \frac12$ both sides hold. -/
theorem forall_norm_le_iff_of_lt_half [CompleteSpace K] (ha : a.IsHermitian) {c : ℝ}
    (hc : 0 < c) (hcoer : a.IsCoerciveWith c) (hθ0 : 0 ≤ θ) (hΔt : 0 < Δt)
    {lmax : ℝ} {w₀ : K} (hw₀ : IsFormEigenpair a lmax w₀)
    (hle : ∀ v, a v v ≤ lmax * ‖v‖ ^ 2) :
    (∀ u u', IsThetaStep a θ Δt 0 0 u u' → ‖u'‖ ≤ ‖u‖) ↔ (1 - 2 * θ) * lmax * Δt ≤ 2 := by
  have hlmax : 0 < lmax := hw₀.pos_of_coercive hc hcoer
  have hden : 0 < 1 + θ * lmax * Δt := by positivity
  constructor
  · intro hstab
    have h := hstab w₀ _ (smul_of_isFormEigenpair hw₀ hΔt.ne' hden.ne')
    rw [norm_smul, Real.norm_eq_abs] at h
    have hr : |(1 - (1 - θ) * lmax * Δt) / (1 + θ * lmax * Δt)| ≤ 1 :=
      le_of_mul_le_mul_right (by simpa using h) (norm_pos_iff.2 hw₀.1)
    rw [abs_div, abs_of_pos hden, div_le_one hden, abs_le] at hr
    linarith [hr.1]
  · intro hcfl u u' h
    exact h.norm_le_of_le_of_lt_half ha (SesqForm.IsCoerciveWith.mono a hcoer hc.le) hle hΔt hcfl

end IsThetaStep

/-! ### The transport form and the upwind discontinuous Galerkin form -/

section Transport

open Polynomial BrokenPolynomial

variable {n : ℕ} {x : Fin (n + 1) → ℝ} {r : ℕ} [hx : Fact (StrictMono x)] {a a₀ : ℝ → ℝ}

/-- For a monotone partition $x_0 < x_1 < \dots < x_n$, every panel $[x_i, x_{i+1}]$ lies in
$[x_0, x_n]$. -/
theorem uIcc_panel_subset (i : Fin n) :
    [[x i.castSucc, x i.succ]] ⊆ [[x 0, x (Fin.last n)]] := by
  have hm : Monotone x := hx.out.monotone
  rw [uIcc_of_le (hm (Fin.castSucc_lt_succ (i := i)).le), uIcc_of_le (hm (Fin.zero_le _))]
  exact Icc_subset_Icc (hm (Fin.zero_le _)) (hm (Fin.le_last _))

/-- If $a$ and $a_0$ are integrable on $[x_0, x_n]$, then for all polynomials $p$ and $q$ the
function $(a p' + a_0 p) q$ is integrable on every panel $[x_i, x_{i+1}]$. -/
theorem intervalIntegrable_transport (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : IntervalIntegrable a₀ volume (x 0) (x (Fin.last n))) (p q : ℝ[X]) (i : Fin n) :
    IntervalIntegrable (fun s => (a s * p.derivative.eval s + a₀ s * p.eval s) * q.eval s) volume
      (x i.castSucc) (x i.succ) :=
  (((ha.mono_set (uIcc_panel_subset i)).mul_continuousOn p.derivative.continuous.continuousOn).add
    ((ha₀.mono_set (uIcc_panel_subset i)).mul_continuousOn
      p.continuous.continuousOn)).mul_continuousOn q.continuous.continuousOn

variable (x r) in
/-- The **transport bilinear map** on the broken polynomial space of a partition $x_0 < \dots < x_n$
with pieces of degree at most $r$:
$$(u, v) \mapsto \sum_i \int_{x_i}^{x_{i+1}} (a u_i' + a_0 u_i) v_i,$$
for coefficients $a$ and $a_0$ that are integrable on $[x_0, x_n]$.

The integrability makes the map bilinear. -/
def transportBilin (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : IntervalIntegrable a₀ volume (x 0) (x (Fin.last n))) :
    BrokenPolynomial x r →ₗ[ℝ] BrokenPolynomial x r →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v => ∑ i, ∫ s in x i.castSucc..x i.succ,
      (a s * (u i).derivative.eval s + a₀ s * (u i).eval s) * (v i).eval s)
    (fun u u' v => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← integral_add (intervalIntegrable_transport ha ha₀ _ _ i)
        (intervalIntegrable_transport ha ha₀ _ _ i)]
      exact integral_congr fun s _ => by
        simp only [BrokenPolynomial.add_apply, derivative_add, eval_add]; ring)
    (fun c u v => by
      rw [smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← integral_const_mul]
      exact integral_congr fun s _ => by
        simp only [BrokenPolynomial.smul_apply, derivative_smul, eval_smul, smul_eq_mul]; ring)
    (fun u v v' => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← integral_add (intervalIntegrable_transport ha ha₀ _ _ i)
        (intervalIntegrable_transport ha ha₀ _ _ i)]
      exact integral_congr fun s _ => by simp only [BrokenPolynomial.add_apply, eval_add]; ring)
    (fun c u v => by
      rw [smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← integral_const_mul]
      exact integral_congr fun s _ => by
        simp only [BrokenPolynomial.smul_apply, eval_smul, smul_eq_mul]; ring)

variable (x r) in
/-- **The transport form** ([quarteroni2000numerical], §13.10.1, the form of the continuous Galerkin
semi-discretization (13.65) of $u_t + a u_x + a_0 u = f$). For a strictly increasing partition
$x_0 < \dots < x_n$ and coefficients $a$ and $a_0$ integrable on $[x_0, x_n]$, it is the bounded
bilinear form
$$b(u, v) = \sum_i \int_{x_i}^{x_{i+1}} (a u_i' + a_0 u_i) v_i$$
on the broken polynomial space `BrokenPolynomial x r` with the $L^2$ inner product.

The coefficient $a_0$ is taken at a fixed time. A reaction coefficient that depends on time
gives the family `t ↦ transportForm x r ha (ha₀ t)`. -/
def transportForm (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : IntervalIntegrable a₀ volume (x 0) (x (Fin.last n))) :
    SesqForm ℝ (BrokenPolynomial x r) :=
  SesqForm.ofBilin (transportBilin x r ha ha₀)

/-- The transport form is the sum of the panel integrals: $b(u, v) = \sum_i \int_{x_i}^{x_{i+1}} (a
u_i' + a_0 u_i) v_i$. -/
theorem transportForm_apply (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : IntervalIntegrable a₀ volume (x 0) (x (Fin.last n))) (u v : BrokenPolynomial x r) :
    transportForm x r ha ha₀ u v = ∑ i, ∫ s in x i.castSucc..x i.succ,
      (a s * (u i).derivative.eval s + a₀ s * (u i).eval s) * (v i).eval s := rfl

variable (x r) in
/-- **The upwind discontinuous Galerkin form** ([quarteroni2000numerical], (13.68)). For a strictly
increasing partition $x_0 < \dots < x_n$ and coefficients $a$ and $a_0$ integrable on
$[x_0, x_n]$, it is the bounded bilinear form
$$b^{DG}(u, v) = \sum_i \int_{x_i}^{x_{i+1}} (a u_i' + a_0 u_i) v_i + \sum_{i < n} a(x_i) [u]_i
  \, v^+(x_i)$$
on the broken polynomial space, with the jump $[u]_i = u^+(x_i) - u^-(x_i)$ and the inflow
convention $u^-(x_0) = 0$ of `BrokenPolynomial.jump`.

The inflow datum $\varphi(t)$ of the book enters the right-hand side as
$a(x_0) \varphi(t) v^+(x_0)$. -/
def dgUpwindForm (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : IntervalIntegrable a₀ volume (x 0) (x (Fin.last n))) :
    SesqForm ℝ (BrokenPolynomial x r) :=
  SesqForm.ofBilin (transportBilin x r ha ha₀
    + ∑ i : Fin n, a (x i.castSucc) • (jumpₗ x r i).smulRight (traceRightₗ x r i))

/-- The upwind form is the transport form plus the jump terms: $b^{DG}(u, v) = b(u, v) + \sum_{i <
n} a(x_i) [u]_i \, v^+(x_i)$. -/
theorem dgUpwindForm_apply (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : IntervalIntegrable a₀ volume (x 0) (x (Fin.last n))) (u v : BrokenPolynomial x r) :
    dgUpwindForm x r ha ha₀ u v
      = transportForm x r ha ha₀ u v
        + ∑ i : Fin n, a (x i.castSucc) * jump u i * traceRight v i := by
  simp only [dgUpwindForm, transportForm, SesqForm.ofBilin_apply, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, jumpₗ_apply,
    traceRightₗ_apply, smul_eq_mul]
  simp only [mul_assoc]

/-- **The energy identity of the upwind discontinuous Galerkin form** ([quarteroni2000numerical],
§13.10.1, the computation behind (13.69)). Let $a$ be differentiable at every point of
$[x_0, x_n]$ with $a'$ continuous on $[x_0, x_n]$, and let $a$ and $a_0$ be integrable on
$[x_0, x_n]$. Then for every broken polynomial $v$,
$$b^{DG}(v, v) = \tfrac12 a(x_n) v^-(x_n)^2 + \tfrac12 \sum_{i < n} a(x_i) [v]_i^2 + \sum_i
  \int_{x_i}^{x_{i+1}} \big(a_0 - \tfrac12 a'\big) v_i^2.$$

The proof integrates by parts on each panel, $\int a v v' = \frac12 [a v^2] - \frac12 \int a'
v^2$ (`BrokenPolynomial.sum_integral_mul_deriv_mul_eq`), and uses $\frac12 a (v^-)^2 - \frac12 a
(v^+)^2 + a [v] v^+ = \frac12 a [v]^2$ at each node. When $a_0 - \frac12 a' \ge 0$ the form is
positive, and the identity is the hypothesis of the dissipative energy estimate with $Q$ the
boundary and jump terms. -/
theorem dgUpwindForm_apply_self (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : IntervalIntegrable a₀ volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n)))) (v : BrokenPolynomial x r) :
    dgUpwindForm x r ha ha₀ v v
      = a (x (Fin.last n)) * traceLeft v (Fin.last n) ^ 2 / 2
        + ∑ i : Fin n, a (x i.castSucc) * jump v i ^ 2 / 2
        + ∑ i, ∫ s in x i.castSucc..x i.succ, (a₀ s - deriv a s / 2) * (v i).eval s ^ 2 := by
  have hm : Monotone x := hx.out.monotone
  have hIcc : ∀ i : Fin n, [[x i.castSucc, x i.succ]] ⊆ Icc (x 0) (x (Fin.last n)) := fun i =>
    (uIcc_panel_subset i).trans (uIcc_of_le (hm (Fin.zero_le _))).le
  -- the panel integrals split into the `a v v'` part and the `a₀ v²` part
  have hsplit : ∀ i : Fin n, ∫ s in x i.castSucc..x i.succ,
      (a s * (v i).derivative.eval s + a₀ s * (v i).eval s) * (v i).eval s
      = (∫ s in x i.castSucc..x i.succ, a s * (v i).eval s * (v i).derivative.eval s)
        + ∫ s in x i.castSucc..x i.succ, a₀ s * (v i).eval s ^ 2 := by
    intro i
    rw [← integral_add]
    · exact integral_congr fun s _ => by ring
    · exact ((ha.mono_set (uIcc_panel_subset i)).mul_continuousOn
        (v i).continuous.continuousOn).mul_continuousOn (v i).derivative.continuous.continuousOn
    · exact (ha₀.mono_set (uIcc_panel_subset i)).mul_continuousOn
        ((v i).continuous.pow 2).continuousOn
  have hibp := sum_integral_mul_deriv_mul_eq hm hd hd' v
  have hsub : ∀ i : Fin n, ∫ s in x i.castSucc..x i.succ, (a₀ s - deriv a s / 2) * (v i).eval s ^ 2
      = (∫ s in x i.castSucc..x i.succ, a₀ s * (v i).eval s ^ 2)
        - (1 / 2) * ∫ s in x i.castSucc..x i.succ, deriv a s * (v i).eval s ^ 2 := by
    intro i
    rw [← integral_const_mul, ← integral_sub]
    · exact integral_congr fun s _ => by ring
    · exact (ha₀.mono_set (uIcc_panel_subset i)).mul_continuousOn
        ((v i).continuous.pow 2).continuousOn
    · exact (((hd'.mono (hIcc i)).intervalIntegrable).mul_continuousOn
        ((v i).continuous.pow 2).continuousOn).const_mul _
  rw [dgUpwindForm_apply, transportForm_apply]
  simp only [hsplit, hsub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hibp]
  have hnode : ∑ i : Fin n, a (x i.castSucc) * jump v i ^ 2 / 2
      = ∑ i : Fin n, a (x i.castSucc) * jump v i * traceRight v i
        - ∑ i : Fin n,
          a (x i.castSucc) * (traceRight v i ^ 2 - traceLeft v i.castSucc ^ 2) / 2 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [jump_apply]; ring
  rw [hnode]
  ring

/-- **The energy identity of the transport form on the continuous subspace**
([quarteroni2000numerical], §13.10.1, the identity behind (13.66)). Let $n > 0$, let $a$ be
differentiable at every point of $[x_0, x_n]$ with $a'$ continuous on $[x_0, x_n]$, and let $a$
and $a_0$ be integrable on $[x_0, x_n]$. Then for every broken polynomial $v$ without jumps at
the interior nodes,
$$b(v, v) = \tfrac12 a(x_n) v^-(x_n)^2 - \tfrac12 a(x_0) v^+(x_0)^2 + \sum_i
  \int_{x_i}^{x_{i+1}} \big(a_0 - \tfrac12 a'\big) v_i^2.$$

This follows from `Variational.dgUpwindForm_apply_self`: the jump terms vanish except at $x_0$,
where $[v]_0 = v^+(x_0)$. -/
theorem transportForm_apply_self_of_continuous
    (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : IntervalIntegrable a₀ volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n)))) (hn : 0 < n)
    {v : BrokenPolynomial x r} (hv : v ∈ continuous x r) :
    transportForm x r ha ha₀ v v
      = a (x (Fin.last n)) * traceLeft v (Fin.last n) ^ 2 / 2
        - a (x 0) * traceRight v ⟨0, hn⟩ ^ 2 / 2
        + ∑ i, ∫ s in x i.castSucc..x i.succ, (a₀ s - deriv a s / 2) * (v i).eval s ^ 2 := by
  have h := dgUpwindForm_apply_self ha ha₀ hd hd' v
  rw [dgUpwindForm_apply] at h
  have hjump : ∀ i : Fin n, i ≠ ⟨0, hn⟩ → jump v i = 0 := fun i hi =>
    hv i (Nat.pos_of_ne_zero fun h0 => hi (Fin.ext h0))
  have h1 : ∑ i : Fin n, a (x i.castSucc) * jump v i * traceRight v i
      = a (x 0) * traceRight v ⟨0, hn⟩ ^ 2 := by
    rw [Finset.sum_eq_single ⟨0, hn⟩ (fun i _ hi => by rw [hjump i hi, mul_zero, zero_mul])
      (fun h => absurd (Finset.mem_univ _) h), jump_zero]
    simp only [sq, mul_assoc]
    rfl
  have h2 : ∑ i : Fin n, a (x i.castSucc) * jump v i ^ 2 / 2
      = a (x 0) * traceRight v ⟨0, hn⟩ ^ 2 / 2 := by
    rw [Finset.sum_eq_single ⟨0, hn⟩ (fun i _ hi => by rw [hjump i hi]; ring)
      (fun h => absurd (Finset.mem_univ _) h), jump_zero]
    rfl
  rw [h1] at h
  rw [h2] at h
  linarith

/-- **Dissipativity of the transport form on a subspace of $V_h^{in}$.** Let $n > 0$, let $a$ be
differentiable at every point of $[x_0, x_n]$ with $a'$ continuous on $[x_0, x_n]$, let $a$ and
$a_0$ be integrable on $[x_0, x_n]$, and let $c \le a_0 - \frac12 a'$ on $[x_0, x_n]$. Let $V$
be a subspace of the broken polynomial space whose elements have no jumps at the interior nodes
and satisfy $v^+(x_0) = 0$. Then for every $v \in V$,
$$c \|v\|^2 + \tfrac12 a(x_n) v^-(x_n)^2 \le b(v, v),$$
where $b$ is the transport form restricted to $V$.

The inflow term of `Variational.transportForm_apply_self_of_continuous` vanishes. -/
theorem le_transportForm_restrict (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : IntervalIntegrable a₀ volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n)))) (hn : 0 < n) {c : ℝ}
    (hc : ∀ s ∈ Icc (x 0) (x (Fin.last n)), c ≤ a₀ s - deriv a s / 2)
    {V : Submodule ℝ (BrokenPolynomial x r)}
    (hV : ∀ v ∈ V, v ∈ continuous x r ∧ traceRight v ⟨0, hn⟩ = 0) (v : V) :
    c * ‖v‖ ^ 2 + a (x (Fin.last n)) * traceLeft (v : BrokenPolynomial x r) (Fin.last n) ^ 2 / 2
      ≤ (transportForm x r ha ha₀).restrict V v v := by
  have hle : x 0 ≤ x (Fin.last n) := hx.out.monotone (Fin.zero_le _)
  have hreac : IntervalIntegrable (fun s => a₀ s - deriv a s / 2) volume (x 0) (x (Fin.last n)) :=
    ha₀.sub (((by rwa [uIcc_of_le hle] :
      ContinuousOn (deriv a) [[x 0, x (Fin.last n)]]).intervalIntegrable).div_const 2)
  have key := transportForm_apply_self_of_continuous ha ha₀ hd hd' hn (hV v v.2).1
  have hlow := mul_norm_sq_le_sum_integral hreac hc (v : BrokenPolynomial x r)
  rw [SesqForm.restrict_apply, key, (hV v v.2).2, ← Submodule.norm_coe]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
    sub_zero]
  linarith

/-- **Dissipativity of the upwind form** ([quarteroni2000numerical], §13.10.1). Let $a$ be
differentiable at every point of $[x_0, x_n]$ with $a'$ continuous on $[x_0, x_n]$, let $a$ and
$a_0$ be integrable on $[x_0, x_n]$, and let $c \le a_0 - \frac12 a'$ on $[x_0, x_n]$. Then for
every broken polynomial $v$,
$$c \|v\|^2 + \tfrac12 a(x_n) v^-(x_n)^2 + \tfrac12 \sum_{i < n} a(x_i) [v]_i^2 \le b^{DG}(v,
  v).$$
-/
theorem le_dgUpwindForm (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : IntervalIntegrable a₀ volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n)))) {c : ℝ}
    (hc : ∀ s ∈ Icc (x 0) (x (Fin.last n)), c ≤ a₀ s - deriv a s / 2) (v : BrokenPolynomial x r) :
    c * ‖v‖ ^ 2 + a (x (Fin.last n)) * traceLeft v (Fin.last n) ^ 2 / 2
        + ∑ i : Fin n, a (x i.castSucc) * jump v i ^ 2 / 2
      ≤ dgUpwindForm x r ha ha₀ v v := by
  have hle : x 0 ≤ x (Fin.last n) := hx.out.monotone (Fin.zero_le _)
  have hreac : IntervalIntegrable (fun s => a₀ s - deriv a s / 2) volume (x 0) (x (Fin.last n)) :=
    ha₀.sub (((by rwa [uIcc_of_le hle] :
      ContinuousOn (deriv a) [[x 0, x (Fin.last n)]]).intervalIntegrable).div_const 2)
  have hlow := mul_norm_sq_le_sum_integral hreac hc v
  rw [dgUpwindForm_apply_self ha ha₀ hd hd' v]
  linarith

end Transport

end Variational

end
