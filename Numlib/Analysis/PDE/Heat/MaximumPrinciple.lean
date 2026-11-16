/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Distributions.TestFunctionApprox
import Numlib.Analysis.PDE.Elliptic.MaximumPrinciple
import Numlib.Analysis.PDE.Heat
import Numlib.MeasureTheory.Function.ContinuousOnClosure

/-!
# The weak maximum principle for the heat equation

Let $\Omega \subseteq \mathbb{R}^N$ be an arbitrary open set, let $A = -\Delta$ be the Dirichlet
Laplacian on $L^2(\Omega)$, and let $u$ be the solution of $u' + Au = 0$, $u(0) = u_0$, in the sense
of `Heat.IsSolution` of `Numlib.Analysis.PDE.Heat`. This module proves Theorem 10.3 of
[brezis2011functional],
$$\min\{0, \inf u_0\} \le u(t) \le \max\{0, \sup u_0\} \quad \text{a.e. on } \Omega, \text{ for all
  } t \ge 0,$$
and Corollary 10.4 (positivity and the $L^\infty$ contraction
$\|u(t)\|_{L^\infty} \le \|u_0\|_{L^\infty}$). The proof is Stampacchia's truncation method in time,
with the truncation function of the proof of Theorem 9.27 of [brezis2011functional].

The module also proves Corollary 10.5 of [brezis2011functional]: on a smooth domain with bounded
boundary, the solution with a continuous datum that vanishes on $\Gamma = \partial \Omega$ (and at
infinity when $\Omega$ is unbounded) is continuous on $\overline{Q} = \overline{\Omega} \times [0,
\infty)$. The classical maximum principle, Theorem 10.6 of [brezis2011functional], is in
`Numlib.Analysis.PDE.Heat.Classical`.

## Main definitions

* `Heat.IsTruncation`: a function $G \in C^1(\mathbb{R})$ with $0 \le G' \le 1$, $G = 0$ on
  $(-\infty, 0]$ and $G > 0$ on $(0, \infty)$.
* `Heat.truncationPrimitive`: the primitive $H(s) = \int_0^s G$.
* `Heat.truncationFunctional`: the functional $\Phi(v) = \int_\Omega H(v - K)$ on $L^2(\Omega)$.
* `Heat.truncationL2`: the truncation $G(v - K)$ as an element of $L^2(\Omega)$.

## Main results

* `Heat.abs_truncationFunctional_sub_sub_inner_le`: $|\Phi(v + w) - \Phi(v) - \langle G(v - K), w
  \rangle| \le \|w\|^2$.
* `Heat.dirichletLaplacian_inner_truncationL2_nonneg`: $\langle Af, G(f - K) \rangle \ge 0$ for
  $f \in D(A)$ and $K \ge 0$.
* `Heat.IsSolution.hasDerivAt_truncationFunctional`: $\frac{d}{dt} \Phi(u(t)) = \langle G(u(t) - K),
  u'(t) \rangle$ for $t > 0$.
* `Heat.IsSolution.le_of_le` and `Heat.IsSolution.ge_of_ge`: Theorem 10.3, the upper and the lower
  bound.
* `Heat.IsSolution.nonneg` and `Heat.IsSolution.eLpNorm_top_le`: Corollary 10.4, positivity and the
  $L^\infty$ contraction.
* `Heat.IsSolution.abs_sub_le_of_abs_sub_le`: the $L^\infty$ contraction (19) between two solutions.
* `Heat.IsSolution.continuousOn_spaceTime_of_isContDiffChartDomain`: Corollary 10.5 on a domain of
  class $C^{2\ell}$ with $N/2 < 2\ell$.
* `Heat.IsSolution.continuousOn_spaceTime`: Corollary 10.5 on a domain of class $C^\infty$.
* `Heat.IsSolution.continuousOn_spaceTime_of_isBounded`: Corollary 10.5 on a bounded domain of class
  $C^\infty$.

## Proof outline

Theorem 10.3 uses three facts. First, a truncation function $G$ has the primitive $H$ with
$0 \le H(s) \le s^2$, so the functional $\Phi(v) = \int_\Omega H(v - K)$ is finite on $L^2(\Omega)$
for $K \ge 0$. Second, the elementary estimate $|H(a) - H(b) - G(b)(a - b)| \le (a - b)^2$ gives the
derivative of $\Phi$ along a $C^1$ curve, $\frac{d}{dt} \Phi(u(t)) = \langle G(u(t) - K), u'(t)
\rangle$. Third, for $v \in H^1_0(\Omega)$ and $K \ge 0$, the function $G(v - K)$ lies in
$H^1_0(\Omega)$ with $\nabla G(v - K) = G'(v - K) \nabla v$; this is the chain rule of Proposition
9.5 of [brezis2011functional], applied to $s \mapsto G(s - K)$, which vanishes at $0$ because
$K \ge 0$. Then $\varphi(t) = \Phi(u(t))$ is continuous on $[0, \infty)$, $\varphi \ge 0$,
$\varphi(0) = 0$ when $u_0 \le K$ a.e., and $\varphi$ is $C^1$ on $(0, \infty)$ with
$$\varphi' = \langle G(u - K), u' \rangle = -\int_\Omega G'(u - K) |\nabla u|^2 \le 0.$$
Hence $\varphi = 0$, that is, $u(t) \le K$ a.e.

For Corollary 10.5, the datum is approximated uniformly on $\Omega$ by test functions
(`exists_testFunction_tendsto_of_continuousOn`, a cut-off to a compact subset of $\Omega$ followed
by a mollification). By Theorem 10.2 of [brezis2011functional] and
`Bochner.continuousOn_spaceTime_of_contDiffOnThrough`, their solutions are continuous on
$\overline{\Omega} \times [0, \infty)$. The $L^\infty$ contraction (19) makes these solutions
uniformly Cauchy on $\overline{\Omega} \times [0, \infty)$.

## Notation

* $\Gamma = \partial \Omega$ is `frontier Ω`, and $\overline{Q} = \overline{\Omega} \times [0,
  \infty)$ is `closure Ω ×ˢ Ici 0`.

## Implementation notes

* $L^2(\Omega)$ is `Lp ℝ 2 (volume.restrict Ω)`, and $A$ is `dirichletLaplacian Ω`.
* Theorem 10.3 is stated for every bound $K \ge 0$ with $u_0 \le K$ a.e. The bound
  $K = \max\{0, \sup u_0\}$ of the source is the least such $K$, and the form with the essential
  supremum follows from this one.
* The derivative of $\Phi$ along a curve comes from the elementary estimate on $H$, not from the
  Fréchet differentiability of a Nemytskii operator.
* Theorem 10.3 and Corollary 10.4 hold on an arbitrary open set $\Omega$. Corollary 10.5 is stated
  on $\mathbb{R}^{d+1}$, that is, for $N = d + 1 \ge 1$.
* The source proves the convergence of the approximating solutions in $L^2$ for Corollary 10.5. This
  is not needed: the semigroup is an $L^\infty$ contraction, so the approximating solutions converge
  almost everywhere.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Convolution Distributions ENNReal Topology InnerProductSpace

noncomputable section

namespace Heat

open LinearPMap LinearPMap.PowDomain SobolevMultiIndex Elliptic

/-! ### The truncation and its primitive -/

/-- A **truncation function** is a function $G \in C^1(\mathbb{R})$ with $0 \le G' \le 1$, $G = 0$
on $(-\infty, 0]$ and $G > 0$ on $(0, \infty)$. It is the function $G$ fixed in the proof of
Theorem 9.27 of [brezis2011functional], which the proof of Theorem 10.3 uses again.

The definition is `IsStampacchiaTruncation` with the bound $M = 1$ on $|G'|$. -/
abbrev IsTruncation (G : ℝ → ℝ) : Prop := IsStampacchiaTruncation G 1

/-- A truncation function exists. An example is `stampacchiaTruncation`. -/
theorem exists_isTruncation : ∃ G : ℝ → ℝ, IsTruncation G :=
  ⟨_, isStampacchiaTruncation_stampacchiaTruncation⟩

variable {G : ℝ → ℝ}

/-- A truncation function $G$ is $1$-Lipschitz: $|G(a) - G(b)| \le |a - b|$ for all
$a, b \in \mathbb{R}$. -/
theorem IsTruncation.abs_sub_le (hG : IsTruncation G) (a b : ℝ) : |G a - G b| ≤ |a - b| := by
  simpa using abs_sub_le_mul_of_abs_deriv_le hG.contDiff hG.abs_deriv_le a b

/-- A truncation function $G$ satisfies $|G(s)| \le |s|$ for all $s \in \mathbb{R}$. -/
theorem IsTruncation.abs_le (hG : IsTruncation G) (s : ℝ) : |G s| ≤ |s| := by
  simpa [hG.zero] using hG.abs_sub_le s 0

/-- A truncation function $G$ satisfies $G(s) \le s$ for all $s \ge 0$. -/
theorem IsTruncation.le_self (hG : IsTruncation G) {s : ℝ} (hs : 0 ≤ s) : G s ≤ s :=
  (le_abs_self _).trans ((hG.abs_le s).trans_eq (abs_of_nonneg hs))

/-- Let $G$ be a truncation function and $K \ge 0$. Then $|G(s - K)| \le |s|$ for all
$s \in \mathbb{R}$: the shift moves the argument towards the region where $G$ vanishes. -/
theorem IsTruncation.abs_apply_sub_le (hG : IsTruncation G) {K : ℝ} (hK : 0 ≤ K) (s : ℝ) :
    |G (s - K)| ≤ |s| := by
  rcases le_or_gt (s - K) 0 with hs | hs
  · rw [hG.eq_zero_of_nonpos _ hs, abs_zero]
    exact abs_nonneg _
  · rw [abs_of_pos (hG.pos_of_pos _ hs)]
    exact (hG.le_self hs.le).trans ((sub_le_self _ hK).trans (le_abs_self _))

/-- The **primitive** of a function $G : \mathbb{R} \to \mathbb{R}$ is
$H(s) = \int_0^s G(\sigma) \, d\sigma$. For a truncation function $G$ it is the function $H$ of
the proof of Theorem 10.3 of [brezis2011functional]. -/
def truncationPrimitive (G : ℝ → ℝ) (s : ℝ) : ℝ := ∫ σ in (0 : ℝ)..s, G σ

/-- For a truncation function $G$, the primitive $H$ is differentiable with $H'(s) = G(s)$ for all
$s \in \mathbb{R}$. -/
theorem hasDerivAt_truncationPrimitive (hG : IsTruncation G) (s : ℝ) :
    HasDerivAt (truncationPrimitive G) (G s) s :=
  (hG.contDiff.continuous.integral_hasStrictDerivAt 0 s).hasDerivAt

/-- For a truncation function $G$, the primitive $H$ is continuous. -/
theorem continuous_truncationPrimitive (hG : IsTruncation G) :
    Continuous (truncationPrimitive G) :=
  continuous_iff_continuousAt.2 fun s ↦ (hasDerivAt_truncationPrimitive hG s).continuousAt

/-- For a truncation function $G$, the primitive satisfies $H(s) = 0$ for all $s \le 0$. -/
theorem truncationPrimitive_of_nonpos (hG : IsTruncation G) {s : ℝ} (hs : s ≤ 0) :
    truncationPrimitive G s = 0 := by
  unfold truncationPrimitive
  refine (intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun σ hσ ↦ ?_).trans
    intervalIntegral.integral_zero
  rw [uIcc_of_ge hs] at hσ
  exact hG.eq_zero_of_nonpos σ hσ.2

/-- For a truncation function $G$, the primitive satisfies $H(s) > 0$ for all $s > 0$. -/
theorem truncationPrimitive_pos (hG : IsTruncation G) {s : ℝ} (hs : 0 < s) :
    0 < truncationPrimitive G s :=
  intervalIntegral.intervalIntegral_pos_of_pos_on (hG.contDiff.continuous.intervalIntegrable _ _)
    (fun σ hσ ↦ hG.pos_of_pos σ hσ.1) hs

/-- For a truncation function $G$, the primitive satisfies $H(s) \ge 0$ for all $s \in \mathbb{R}$.
-/
theorem truncationPrimitive_nonneg (hG : IsTruncation G) (s : ℝ) :
    0 ≤ truncationPrimitive G s := by
  rcases le_or_gt s 0 with hs | hs
  · rw [truncationPrimitive_of_nonpos hG hs]
  · exact (truncationPrimitive_pos hG hs).le

/-- For a truncation function $G$, if $H(s) = 0$, then $s \le 0$. -/
theorem le_zero_of_truncationPrimitive_eq_zero (hG : IsTruncation G) {s : ℝ}
    (h : truncationPrimitive G s = 0) : s ≤ 0 := by
  by_contra hs
  exact (truncationPrimitive_pos hG (not_le.1 hs)).ne' h

/-- For a truncation function $G$, the primitive satisfies $H(s) \le s^2$ for all
$s \in \mathbb{R}$, because $G(\sigma) \le \sigma$ on $[0, s]$. -/
theorem truncationPrimitive_le_sq (hG : IsTruncation G) (s : ℝ) :
    truncationPrimitive G s ≤ s ^ 2 := by
  rcases le_or_gt s 0 with hs | hs
  · rw [truncationPrimitive_of_nonpos hG hs]
    positivity
  · have h1 : ‖∫ σ in (0 : ℝ)..s, G σ‖ ≤ s * |s - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun σ hσ ↦ by
        rw [uIoc_of_le hs.le] at hσ
        rw [Real.norm_eq_abs, abs_of_nonneg (hG.nonneg σ)]
        exact (hG.le_self hσ.1.le).trans hσ.2
    rw [sub_zero, abs_of_pos hs, ← sq] at h1
    exact (le_abs_self _).trans h1

/-- **The second-order bound for the primitive.** For a truncation function $G$ and all
$a, b \in \mathbb{R}$,
$$|H(a) - H(b) - G(b)(a - b)| \le (a - b)^2.$$
The proof writes $H(a) - H(b) - G(b)(a - b) = \int_b^a (G(\sigma) - G(b)) \, d\sigma$ and uses
the Lipschitz bound on $G$. -/
theorem abs_truncationPrimitive_sub_sub_le (hG : IsTruncation G) (a b : ℝ) :
    |truncationPrimitive G a - truncationPrimitive G b - G b * (a - b)| ≤ (a - b) ^ 2 := by
  have hI : ∀ x y : ℝ, IntervalIntegrable G volume x y := fun x y ↦
    hG.contDiff.continuous.intervalIntegrable x y
  have h1 : truncationPrimitive G a - truncationPrimitive G b = ∫ σ in b..a, G σ :=
    intervalIntegral.integral_interval_sub_left (hI 0 a) (hI 0 b)
  have h2 : G b * (a - b) = ∫ σ in b..a, G b := by
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
  rw [h1, h2, ← intervalIntegral.integral_sub (hI b a) (intervalIntegrable_const)]
  have h3 : ‖∫ σ in b..a, (G σ - G b)‖ ≤ |a - b| * |a - b| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun σ hσ ↦ by
      rw [Real.norm_eq_abs]
      refine (hG.abs_sub_le σ b).trans ?_
      rcases le_or_gt b a with hba | hab
      · rw [uIoc_of_le hba] at hσ
        rw [abs_of_nonneg (by linarith [hσ.1]), abs_of_nonneg (by linarith)]
        linarith [hσ.2]
      · rw [uIoc_of_ge hab.le] at hσ
        rw [abs_of_nonpos (by linarith [hσ.2]), abs_of_neg (by linarith)]
        linarith [hσ.1]
  rw [Real.norm_eq_abs] at h3
  calc |∫ σ in b..a, (G σ - G b)| ≤ |a - b| * |a - b| := h3
    _ = (a - b) ^ 2 := by rw [← sq, sq_abs]

/-- Let $G$ be a truncation function and $K \ge 0$. Then $H(s - K) \le s^2$ for all
$s \in \mathbb{R}$. Together with $H \ge 0$, this bounds the integrand of the truncation
functional by $s^2$. -/
theorem truncationPrimitive_sub_le_sq (hG : IsTruncation G) {K : ℝ} (hK : 0 ≤ K) (s : ℝ) :
    truncationPrimitive G (s - K) ≤ s ^ 2 := by
  rcases le_or_gt (s - K) 0 with hs | hs
  · rw [truncationPrimitive_of_nonpos hG hs]
    positivity
  · refine (truncationPrimitive_le_sq hG _).trans ?_
    nlinarith

/-! ### The truncation functional $\Phi(v) = \int_\Omega H(v - K)$ on $L^2(\Omega)$ -/

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- For $v \in L^2(\Omega)$, the function $v^2$ is integrable on $\Omega$. -/
theorem integrable_sq (v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    Integrable (fun x ↦ v x ^ 2) (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  (memLp_two_iff_integrable_sq (Lp.aestronglyMeasurable v)).1 (Lp.memLp v)

/-- Let $G$ be a truncation function, $K \ge 0$ and $v \in L^2(\Omega)$. Then the function
$x \mapsto H(v(x) - K)$ is integrable on $\Omega$, because it is measurable and bounded by
$v^2$. -/
theorem integrable_truncationPrimitive_sub (hG : IsTruncation G) {K : ℝ} (hK : 0 ≤ K)
    (v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    Integrable (fun x ↦ truncationPrimitive G (v x - K))
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
  refine (integrable_sq v).mono' ((continuous_truncationPrimitive hG).comp_aestronglyMeasurable
    ((Lp.aestronglyMeasurable v).sub aestronglyMeasurable_const)) (Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_of_nonneg (truncationPrimitive_nonneg hG _)]
  exact truncationPrimitive_sub_le_sq hG hK _

variable (Ω) in
/-- The **truncation functional** of a function $G$ and a number $K$ is the function on
$L^2(\Omega)$
$$\Phi(v) = \int_\Omega H(v(x) - K) \, dx,$$
where $H$ is the primitive of $G$. It is the functional of the proof of Theorem 10.3 of
[brezis2011functional], where $\varphi(t) = \Phi(u(t))$. -/
def truncationFunctional (G : ℝ → ℝ) (K : ℝ)
    (v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) : ℝ :=
  ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), truncationPrimitive G (v x - K)

/-- For a truncation function $G$ and every $K \in \mathbb{R}$, the truncation functional satisfies
$\Phi(v) \ge 0$ for all $v \in L^2(\Omega)$. -/
theorem truncationFunctional_nonneg (hG : IsTruncation G) (K : ℝ)
    (v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    0 ≤ truncationFunctional Ω G K v :=
  integral_nonneg fun _ ↦ truncationPrimitive_nonneg hG _

/-- For a truncation function $G$ and $v \in L^2(\Omega)$, if $v \le K$ almost everywhere on
$\Omega$, then $\Phi(v) = 0$. -/
theorem truncationFunctional_eq_zero_of_ae_le (hG : IsTruncation G) {K : ℝ}
    {v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hv : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), v x ≤ K) :
    truncationFunctional Ω G K v = 0 := by
  unfold truncationFunctional
  rw [integral_eq_zero_of_ae]
  filter_upwards [hv] with x hx
  exact truncationPrimitive_of_nonpos hG (by linarith)

/-- Let $G$ be a truncation function, $K \ge 0$ and $v \in L^2(\Omega)$. If $\Phi(v) = 0$, then
$v \le K$ almost everywhere on $\Omega$. The proof uses that the nonnegative integrand
$H(v - K)$ vanishes almost everywhere, and that $H(s) = 0$ only for $s \le 0$. -/
theorem ae_le_of_truncationFunctional_eq_zero (hG : IsTruncation G) {K : ℝ} (hK : 0 ≤ K)
    {v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (h : truncationFunctional Ω G K v = 0) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), v x ≤ K := by
  have := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall fun x ↦ truncationPrimitive_nonneg hG (v x - K))
    (integrable_truncationPrimitive_sub hG hK v)).1 h
  filter_upwards [this] with x hx
  have := le_zero_of_truncationPrimitive_eq_zero hG hx
  linarith

/-- Let $G$ be a truncation function, $K \ge 0$ and $v \in L^2(\Omega)$. Then
$x \mapsto G(v(x) - K)$ lies in $L^2(\Omega)$, because $|G(s - K)| \le |s|$. -/
theorem memLp_truncation_sub (hG : IsTruncation G) {K : ℝ} (hK : 0 ≤ K)
    (v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    MemLp (fun x ↦ G (v x - K)) 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
  refine (Lp.memLp v).of_ae_norm_le_mul (hG.contDiff.continuous.comp_aestronglyMeasurable
    ((Lp.aestronglyMeasurable v).sub aestronglyMeasurable_const)) (c := 1)
    (Eventually.of_forall fun x ↦ ?_)
  rw [one_mul]
  exact hG.abs_apply_sub_le hK (v x)

variable (Ω) in
/-- For a truncation function $G$, $K \ge 0$ and $v \in L^2(\Omega)$, the **truncation** $G(v - K)$
as an element of $L^2(\Omega)$. In the proof of Theorem 10.3 of [brezis2011functional] it is
$G(u(t) - K)$. -/
def truncationL2 (hG : IsTruncation G) {K : ℝ} (hK : 0 ≤ K)
    (v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  (memLp_truncation_sub hG hK v).toLp _

/-- The truncation `Heat.truncationL2` of $v$ agrees almost everywhere on $\Omega$ with
$x \mapsto G(v(x) - K)$. -/
theorem coeFn_truncationL2 (hG : IsTruncation G) {K : ℝ} (hK : 0 ≤ K)
    (v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ⇑(truncationL2 Ω hG hK v) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      fun x ↦ G (v x - K) :=
  (memLp_truncation_sub hG hK v).coeFn_toLp

/-- For a truncation function $G$, $K \ge 0$ and $v \in L^2(\Omega)$, the truncation satisfies
$\|G(v - K)\| \le \|v\|$ in $L^2(\Omega)$. -/
theorem norm_truncationL2_le (hG : IsTruncation G) {K : ℝ} (hK : 0 ≤ K)
    (v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ‖truncationL2 Ω hG hK v‖ ≤ ‖v‖ := by
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [coeFn_truncationL2 hG hK v] with x hx
  rw [hx, Real.norm_eq_abs, Real.norm_eq_abs]
  exact hG.abs_apply_sub_le hK (v x)

/-- **The key estimate for the truncation functional.** Let $G$ be a truncation function and
$K \ge 0$. For all $v, w \in L^2(\Omega)$,
$$|\Phi(v + w) - \Phi(v) - \langle G(v - K), w \rangle| \le \|w\|^2.$$
This is the step of the proof of Theorem 10.3 of [brezis2011functional] that differentiates
$\varphi$. The proof integrates the pointwise bound $|H(a) - H(b) - G(b)(a - b)| \le (a - b)^2$. -/
theorem abs_truncationFunctional_sub_sub_inner_le (hG : IsTruncation G) {K : ℝ} (hK : 0 ≤ K)
    (v w : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    |truncationFunctional Ω G K (v + w) - truncationFunctional Ω G K v
      - ⟪truncationL2 Ω hG hK v, w⟫_ℝ| ≤ ‖w‖ ^ 2 := by
  have h1 := integrable_truncationPrimitive_sub hG hK (v + w)
  have h2 := integrable_truncationPrimitive_sub hG hK v
  have h3 : Integrable (fun x ↦ truncationL2 Ω hG hK v x * w x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    (L2.integrable_inner (𝕜 := ℝ) (truncationL2 Ω hG hK v) w).congr
      (Eventually.of_forall fun x ↦ by simp [RCLike.inner_apply, mul_comm])
  have h12 : Integrable (fun x ↦ truncationPrimitive G ((v + w) x - K)
      - truncationPrimitive G (v x - K)) (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    h1.sub h2
  have h123 : Integrable (fun x ↦ truncationPrimitive G ((v + w) x - K)
      - truncationPrimitive G (v x - K) - truncationL2 Ω hG hK v x * w x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := h12.sub h3
  rw [L2.inner_eq_integral_mul, truncationFunctional, truncationFunctional, ← integral_sub h1 h2,
    ← integral_sub h12 h3, L2.norm_sq_eq_integral_sq]
  refine (abs_integral_le_integral_abs).trans (integral_mono_ae h123.abs (integrable_sq w) ?_)
  filter_upwards [Lp.coeFn_add v w, coeFn_truncationL2 hG hK v] with x hx1 hx2
  rw [hx1, Pi.add_apply, hx2]
  have := abs_truncationPrimitive_sub_sub_le hG (v x + w x - K) (v x - K)
  rwa [show v x + w x - K - (v x - K) = w x by ring] at this

/-- **The truncation functional is Lipschitz on bounded sets.** Let $G$ be a truncation function and
$K \ge 0$. For all $v, w \in L^2(\Omega)$,
$$|\Phi(w) - \Phi(v)| \le \|v\| \|w - v\| + \|w - v\|^2.$$
-/
theorem abs_truncationFunctional_sub_le (hG : IsTruncation G) {K : ℝ} (hK : 0 ≤ K)
    (v w : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    |truncationFunctional Ω G K w - truncationFunctional Ω G K v|
      ≤ ‖v‖ * ‖w - v‖ + ‖w - v‖ ^ 2 := by
  have h1 := abs_truncationFunctional_sub_sub_inner_le hG hK v (w - v)
  rw [add_sub_cancel] at h1
  have h2 : |⟪truncationL2 Ω hG hK v, w - v⟫_ℝ| ≤ ‖v‖ * ‖w - v‖ :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (norm_truncationL2_le hG hK v) (norm_nonneg _))
  calc |truncationFunctional Ω G K w - truncationFunctional Ω G K v|
      = |(truncationFunctional Ω G K w - truncationFunctional Ω G K v
          - ⟪truncationL2 Ω hG hK v, w - v⟫_ℝ) + ⟪truncationL2 Ω hG hK v, w - v⟫_ℝ| := by
        congr 1
        ring
    _ ≤ |truncationFunctional Ω G K w - truncationFunctional Ω G K v
          - ⟪truncationL2 Ω hG hK v, w - v⟫_ℝ| + |⟪truncationL2 Ω hG hK v, w - v⟫_ℝ| :=
        abs_add_le _ _
    _ ≤ ‖w - v‖ ^ 2 + ‖v‖ * ‖w - v‖ := add_le_add h1 h2
    _ = ‖v‖ * ‖w - v‖ + ‖w - v‖ ^ 2 := add_comm _ _

/-- For a truncation function $G$ and $K \ge 0$, the truncation functional $\Phi$ is continuous on
$L^2(\Omega)$. -/
theorem continuous_truncationFunctional (hG : IsTruncation G) {K : ℝ} (hK : 0 ≤ K) :
    Continuous (truncationFunctional Ω G K) := by
  refine continuous_iff_continuousAt.2 fun v ↦ ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun w ↦ ‖v‖ * ‖w - v‖ + ‖w - v‖ ^ 2) (𝓝 v) (𝓝 (‖v‖ * 0 + 0 ^ 2)) := by
    have h0 : Tendsto (fun w ↦ ‖w - v‖) (𝓝 v) (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 tendsto_id
    exact (h0.const_mul _).add (h0.pow 2)
  rw [mul_zero, zero_pow two_ne_zero, add_zero] at hlim
  exact squeeze_zero (fun _ ↦ norm_nonneg _)
    (fun w ↦ (Real.norm_eq_abs _).trans_le (abs_truncationFunctional_sub_le hG hK v w)) hlim

/-! ### The truncation of an $H^1_0$ function, and $\langle Au, G(u - K) \rangle \ge 0$ -/

/-- **The truncation of an $H^1_0$ function.** Let $G$ be a truncation function, $K \ge 0$, and
$v \in H^1_0(\Omega)$. Then there is $w \in H^1_0(\Omega)$ such that $w = G(v - K)$ almost
everywhere on $\Omega$ and, for each $i$,
$$\partial_i w = G'(v - K) \, \partial_i v \quad \text{almost everywhere on } \Omega.$$

The proof is the chain rule of Proposition 9.5 of [brezis2011functional] with
`SobolevMultiIndexZero.contDiff_comp_mem`, applied to $s \mapsto G(s - K)$, which vanishes at
$0$ because $K \ge 0$. -/
theorem truncation_comp_mem_sobolevZero (hG : IsTruncation G) {K : ℝ} (hK : 0 ≤ K)
    {v : SobolevEuclidean N 1 2 Ω} (hv : v ∈ SobolevEuclideanZero N 1 2 Ω) :
    ∃ w : SobolevEuclidean N 1 2 Ω, w ∈ SobolevEuclideanZero N 1 2 Ω ∧
      fn w =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] (fun x ↦ G (fn v x - K)) ∧
      ∀ i, (weakDeriv w (MultiIndexLE.single i) : EuclideanSpace ℝ (Fin N) → ℝ)
        =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
          fun x ↦ deriv G (fn v x - K) * weakDeriv v (MultiIndexLE.single i) x := by
  obtain ⟨w, hw⟩ := exists_truncation_elem hG v (Or.inr hK)
  refine ⟨w, ?_, hw, fun i ↦ weakDeriv_single_ae_eq_of_fn_ae_eq_truncation hG hw i⟩
  exact SobolevMultiIndexZero.contDiff_comp_mem ENNReal.ofNat_ne_top hv (hG.contDiff_sub K)
    (by rw [zero_sub]; exact hG.eq_zero_of_nonpos (-K) (by linarith)) (hG.abs_deriv_sub_le K) hw

/-- Let $G$ be a truncation function, $K \in \mathbb{R}$, and $v, w \in H^1(\Omega)$ with
$\partial_i w = G'(v - K) \, \partial_i v$ almost everywhere on $\Omega$ for each $i$. Then
$$\int_\Omega \nabla v \cdot \nabla w \ge 0.$$
The integrand equals $G'(v - K) |\nabla v|^2 \ge 0$ almost everywhere. The left side is
`Elliptic.dirichletForm`. The element $w$ of `Heat.truncation_comp_mem_sobolevZero` satisfies
the hypothesis. -/
theorem dirichletForm_truncation_nonneg (hG : IsTruncation G) {K : ℝ}
    {v w : SobolevEuclidean N 1 2 Ω}
    (hw : ∀ i, (weakDeriv w (MultiIndexLE.single i) : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        fun x ↦ deriv G (fn v x - K) * weakDeriv v (MultiIndexLE.single i) x) :
    0 ≤ dirichletForm Ω v w := by
  rw [dirichletForm_apply]
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_all_iff.2 hw] with x hx
  refine Finset.sum_nonneg fun i _ ↦ ?_
  rw [hx i, mul_comm, mul_assoc]
  exact mul_nonneg (hG.deriv_nonneg _) (mul_self_nonneg _)

/-- Let $G$ be a truncation function and $K \ge 0$. For every $f \in D(A)$,
$$\langle Af, G(f - K) \rangle \ge 0.$$
This is the step $\int G(u - K) \Delta u = -\int G'(u - K) |\nabla u|^2 \le 0$ of the proof of
Theorem 10.3 of [brezis2011functional]. The truncation $G(f - K)$ is the function of an element
of $H^1_0(\Omega)$, and the definition of $A$ gives $\langle Af, G(f - K) \rangle = \int_\Omega
\nabla f \cdot \nabla G(f - K)$. -/
theorem dirichletLaplacian_inner_truncationL2_nonneg (hG : IsTruncation G) {K : ℝ} (hK : 0 ≤ K)
    (f : (dirichletLaplacian Ω).domain) :
    0 ≤ ⟪dirichletLaplacian Ω f, truncationL2 Ω hG hK f⟫_ℝ := by
  obtain ⟨v, hv, hvf⟩ := dirichletLaplacian_exists_lift f
  obtain ⟨w, hw, hwv, hwd⟩ := truncation_comp_mem_sobolevZero hG hK hv
  have hfv : (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fn v :=
    Filter.EventuallyEq.of_eq (congrArg (fun z : Lp ℝ 2 (volume.restrict
      (Ω : Set (EuclideanSpace ℝ (Fin N)))) ↦ (z : EuclideanSpace ℝ (Fin N) → ℝ)) hvf.symm)
  have he : truncationL2 Ω hG hK f = fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
      volume w := by
    refine Lp.ext ?_
    filter_upwards [coeFn_truncationL2 hG hK f, hwv, hfv] with x hx1 hx2 hx3
    rw [hx1, fnL_apply, hx2, hx3]
  rw [he, dirichletLaplacian_inner_eq_dirichletForm f hv hvf hw]
  exact dirichletForm_truncation_nonneg hG hwd

/-! ### Theorem 10.3 -/

namespace IsSolution

variable {u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}

/-- Let $u$ be the solution of the heat equation with datum $u_0$, let $G$ be a truncation function
and $K \ge 0$. Then $t \mapsto \Phi(u(t))$ is continuous on $[0, \infty)$. -/
theorem continuousOn_truncationFunctional (h : IsSolution Ω u₀ u) (hG : IsTruncation G) {K : ℝ}
    (hK : 0 ≤ K) : ContinuousOn (fun t ↦ truncationFunctional Ω G K (u t)) (Ici 0) :=
  (continuous_truncationFunctional hG hK).comp_continuousOn h.continuousOn

/-- **The derivative of $\varphi(t) = \Phi(u(t))$.** Let $u$ be the solution of the heat equation
with datum $u_0$, let $G$ be a truncation function, $K \ge 0$, and $t > 0$. Then $\varphi$ is
differentiable at $t$ with
$$\varphi'(t) = \langle G(u(t) - K), u'(t) \rangle.$$
This is (18) in the proof of Theorem 10.3 of [brezis2011functional].

The proof uses the key estimate $|\Phi(u(t')) - \Phi(u(t)) - \langle G(u(t) - K), u(t') - u(t)
\rangle| \le \|u(t') - u(t)\|^2$, which is $o(t' - t)$, and the differentiability of
$t' \mapsto \langle G(u(t) - K), u(t') \rangle$. -/
theorem hasDerivAt_truncationFunctional (h : IsSolution Ω u₀ u) (hG : IsTruncation G) {K : ℝ}
    (hK : 0 ≤ K) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t ↦ truncationFunctional Ω G K (u t))
      ⟪truncationL2 Ω hG hK (u t), deriv u t⟫_ℝ t := by
  set g := truncationL2 Ω hG hK (u t) with hg
  rw [hasDerivAt_iff_isLittleO]
  -- the quadratic remainder
  have hA : (fun t' ↦ truncationFunctional Ω G K (u t') - truncationFunctional Ω G K (u t)
      - ⟪g, u t' - u t⟫_ℝ) =o[𝓝 t] fun t' ↦ t' - t := by
    have hO : (fun t' ↦ u t' - u t) =O[𝓝 t] fun t' ↦ t' - t := (h.hasDerivAt ht).isBigO_sub
    have h0 : (fun t' ↦ ‖u t' - u t‖) =o[𝓝 t] fun _ ↦ (1 : ℝ) := by
      rw [Asymptotics.isLittleO_one_iff]
      exact tendsto_iff_norm_sub_tendsto_zero.1 (h.hasDerivAt ht).continuousAt.tendsto
    have hsq : (fun t' ↦ ‖u t' - u t‖ * ‖u t' - u t‖) =o[𝓝 t] fun t' ↦ (t' - t) * 1 :=
      hO.norm_left.mul_isLittleO h0
    refine (Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun t' ↦ ?_)).trans_isLittleO
      (hsq.congr_right fun t' ↦ mul_one _)
    rw [one_mul, Real.norm_eq_abs, Real.norm_of_nonneg (mul_self_nonneg _), ← sq]
    have := abs_truncationFunctional_sub_sub_inner_le hG hK (u t) (u t' - u t)
    rwa [add_sub_cancel] at this
  -- the linear part
  have hB : (fun t' ↦ ⟪g, u t' - u t⟫_ℝ - (t' - t) • ⟪g, deriv u t⟫_ℝ) =o[𝓝 t]
      fun t' ↦ t' - t := by
    have hd : HasDerivAt (fun t' ↦ ⟪g, u t'⟫_ℝ) ⟪g, deriv u t⟫_ℝ t := by
      have := (hasDerivAt_const t g).inner ℝ (h.hasDerivAt ht)
      rw [inner_zero_left, add_zero, ← h.deriv_eq ht] at this
      exact this
    refine (hasDerivAt_iff_isLittleO.1 hd).congr_left fun t' ↦ ?_
    rw [inner_sub_right]
  refine (hA.add hB).congr_left fun t' ↦ ?_
  ring

/-- Let $u$ be the solution of the heat equation with datum $u_0$, let $G$ be a truncation function,
$K \ge 0$, and $t > 0$. Then $\langle G(u(t) - K), u'(t) \rangle \le 0$, because this number
equals $-\langle Au(t), G(u(t) - K) \rangle$. -/
theorem inner_truncationL2_deriv_nonpos (h : IsSolution Ω u₀ u) (hG : IsTruncation G) {K : ℝ}
    (hK : 0 ≤ K) {t : ℝ} (ht : 0 < t) :
    ⟪truncationL2 Ω hG hK (u t), deriv u t⟫_ℝ ≤ 0 := by
  rw [h.deriv_eq ht, inner_neg_right, real_inner_comm, neg_nonpos]
  exact dirichletLaplacian_inner_truncationL2_nonneg hG hK ⟨u t, h.mem_domain ht⟩

/-- Let $u$ be the solution of the heat equation with datum $u_0$, let $G$ be a truncation function
and $K \ge 0$. Then $\varphi(t) = \Phi(u(t))$ is nonincreasing on $[0, \infty)$. -/
theorem antitoneOn_truncationFunctional (h : IsSolution Ω u₀ u) (hG : IsTruncation G) {K : ℝ}
    (hK : 0 ≤ K) : AntitoneOn (fun t ↦ truncationFunctional Ω G K (u t)) (Ici 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0) (h.continuousOn_truncationFunctional hG hK)
    ?_ ?_
  · rw [interior_Ici]
    intro t ht
    exact (h.hasDerivAt_truncationFunctional hG hK ht).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro t ht
    rw [(h.hasDerivAt_truncationFunctional hG hK ht).deriv]
    exact h.inner_truncationL2_deriv_nonpos hG hK ht

/-- **Upper bound of the weak maximum principle.** Let $\Omega \subseteq \mathbb{R}^N$ be open, let
$u$ be the solution of the heat equation with datum $u_0 \in L^2(\Omega)$, and let $K \ge 0$
with $u_0 \le K$ almost everywhere on $\Omega$. Then for every $t \ge 0$, $u(t) \le K$ almost
everywhere on $\Omega$. This is the upper bound of Theorem 10.3 of [brezis2011functional].

The bound $K = \max\{0, \sup u_0\}$ of the source is the least admissible $K$. The proof is
Stampacchia's truncation in time: $\varphi(t) = \int_\Omega H(u(t) - K)$ is continuous on
$[0, \infty)$, nonincreasing, nonnegative and $\varphi(0) = 0$, so $\varphi = 0$ and
$H(u(t) - K) = 0$ almost everywhere. -/
theorem le_of_le (h : IsSolution Ω u₀ u) {K : ℝ} (hK : 0 ≤ K)
    (hu₀ : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), u₀ x ≤ K) {t : ℝ}
    (ht : 0 ≤ t) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), u t x ≤ K := by
  obtain ⟨G, hG⟩ := exists_isTruncation
  have h0 : truncationFunctional Ω G K (u 0) = 0 := by
    rw [h.apply_zero]
    exact truncationFunctional_eq_zero_of_ae_le hG hu₀
  have hle : truncationFunctional Ω G K (u t) ≤ truncationFunctional Ω G K (u 0) :=
    h.antitoneOn_truncationFunctional hG hK self_mem_Ici ht ht
  rw [h0] at hle
  exact ae_le_of_truncationFunctional_eq_zero hG hK
    (le_antisymm hle (truncationFunctional_nonneg hG K _))

/-- If $u$ is the solution of the heat equation with datum $u_0$, then $-u$ is the solution with
datum $-u_0$. -/
theorem neg (h : IsSolution Ω u₀ u) : IsSolution Ω (-u₀) (-u) where
  toIsSolutionOn :=
    { apply_zero := by rw [Pi.neg_apply, h.apply_zero]
      mem_domain := fun t ht ↦ neg_mem (h.mem_domain ht)
      hasDerivWithinAt := fun t ht ↦ by
        have h1 := (h.hasDerivAt ht).neg.hasDerivWithinAt (s := Ioi 0)
        refine h1.congr_deriv ?_
        have e : (⟨(-u) t, neg_mem (h.mem_domain ht)⟩ : (dirichletLaplacian Ω).domain)
            = -⟨u t, h.mem_domain ht⟩ := Subtype.ext rfl
        rw [neg_neg, e, LinearPMap.map_neg, neg_neg] }
  continuousOn := h.continuousOn.neg
  contDiffOn := h.contDiffOn.neg

/-- **Lower bound of the weak maximum principle.** Let $u$ be the solution of the heat equation with
datum $u_0 \in L^2(\Omega)$, and let $K \ge 0$ with $-K \le u_0$ almost everywhere on $\Omega$.
Then for every $t \ge 0$, $-K \le u(t)$ almost everywhere on $\Omega$. This is the lower bound
of Theorem 10.3 of [brezis2011functional].

The proof applies `Heat.IsSolution.le_of_le` to $-u$. -/
theorem ge_of_ge (h : IsSolution Ω u₀ u) {K : ℝ} (hK : 0 ≤ K)
    (hu₀ : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), -K ≤ u₀ x) {t : ℝ}
    (ht : 0 ≤ t) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), -K ≤ u t x := by
  have h1 := h.neg.le_of_le hK (K := K) ?_ ht
  · filter_upwards [h1, Lp.coeFn_neg (u t)] with x hx hx'
    rw [Pi.neg_apply, hx', Pi.neg_apply] at hx
    linarith
  · filter_upwards [hu₀, Lp.coeFn_neg u₀] with x hx hx'
    rw [hx', Pi.neg_apply]
    linarith

/-- **Positivity.** Let $u$ be the solution of the heat equation with datum $u_0 \in L^2(\Omega)$.
If $u_0 \ge 0$ almost everywhere on $\Omega$, then for every $t \ge 0$, $u(t) \ge 0$ almost
everywhere on $\Omega$. This is Corollary 10.4(i) of [brezis2011functional]. -/
theorem nonneg (h : IsSolution Ω u₀ u)
    (hu₀ : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), 0 ≤ u₀ x) {t : ℝ}
    (ht : 0 ≤ t) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), 0 ≤ u t x := by
  have := h.ge_of_ge le_rfl (K := 0) (by simpa using hu₀) ht
  simpa using this

/-- **The $L^\infty$ contraction.** Let $u$ be the solution of the heat equation with datum
$u_0 \in L^2(\Omega)$. Then for every $t \ge 0$,
$$\|u(t)\|_{L^\infty(\Omega)} \le \|u_0\|_{L^\infty(\Omega)}.$$
This is Corollary 10.4(ii) of [brezis2011functional]. The bound $\|u\|_{L^\infty(Q)} \le
\|u_0\|_{L^\infty(\Omega)}$ of the source is this bound for every $t$.

The norms are the extended norms `eLpNorm _ ∞`. The bound holds trivially when
$u_0 \notin L^\infty(\Omega)$, where the right side is $\infty$. Otherwise the proof applies
both bounds of Theorem 10.3 with $K = \|u_0\|_{L^\infty}$. -/
theorem eLpNorm_top_le (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 ≤ t) :
    eLpNorm (u t) ∞ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
      ≤ eLpNorm u₀ ∞ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
  rw [eLpNorm_exponent_top (Lp.aestronglyMeasurable _),
    eLpNorm_exponent_top (Lp.aestronglyMeasurable _)]
  rcases eq_or_ne (eLpNormEssSup u₀ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) ⊤
    with htop | hne
  · rw [htop]
    exact le_top
  set K := (eLpNormEssSup u₀ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal
    with hK
  have hK0 : 0 ≤ K := ENNReal.toReal_nonneg
  have hb : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), |u₀ x| ≤ K := by
    filter_upwards [ae_le_eLpNormEssSup (f := u₀)
      (μ := volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))] with x hx
    rw [Real.enorm_eq_ofReal_abs] at hx
    exact (ENNReal.ofReal_le_iff_le_toReal hne).1 hx
  have h1 := h.le_of_le hK0 (hb.mono fun x hx ↦ (le_abs_self _).trans hx) ht
  have h2 := h.ge_of_ge hK0 (hb.mono fun x hx ↦ (abs_le.1 hx).1) ht
  calc eLpNormEssSup (u t) (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
      ≤ ENNReal.ofReal K := by
        refine eLpNormEssSup_le_of_ae_bound ?_
        filter_upwards [h1, h2] with x hx1 hx2
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨hx2, hx1⟩
    _ = eLpNormEssSup u₀ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
        ENNReal.ofReal_toReal hne

end IsSolution


/-! ### Corollary 10.5: continuity on $\overline{Q}$ for continuous data vanishing on $\Gamma$ -/

namespace IsSolution

variable {u₀ v₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {u v : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}

/-- **The $L^\infty$ contraction between two solutions.** Let $u$ and $v$ be the solutions of the
heat equation with data $u_0, v_0 \in L^2(\Omega)$, and let $C \ge 0$ with $|u_0 - v_0| \le C$
almost everywhere on $\Omega$. Then for every $t \ge 0$, $|u(t) - v(t)| \le C$ almost everywhere
on $\Omega$. This is (19) of [brezis2011functional], in the form used in the proof of Corollary
10.5.

The open set $\Omega$ is arbitrary. The proof applies Theorem 10.3 to the solution $u - v$ with
datum $u_0 - v_0$, by the linearity of the semigroup. -/
theorem abs_sub_le_of_abs_sub_le (h : IsSolution Ω u₀ u) (h' : IsSolution Ω v₀ v) {C : ℝ}
    (hC : 0 ≤ C)
    (hb : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), |u₀ x - v₀ x| ≤ C)
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), |u t x - v t x| ≤ C := by
  have hs := isSolution_solution (Ω := Ω) (u₀ - v₀)
  have hb' : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      |(u₀ - v₀) x| ≤ C := by
    filter_upwards [hb, Lp.coeFn_sub u₀ v₀] with x hx hx'
    rw [hx', Pi.sub_apply]
    exact hx
  have h1 := hs.le_of_le hC (hb'.mono fun x hx ↦ (abs_le.1 hx).2) ht
  have h2 := hs.ge_of_ge hC (hb'.mono fun x hx ↦ (abs_le.1 hx).1) ht
  rw [solution_sub] at h1 h2
  rw [h.eqOn_solution ht, h'.eqOn_solution ht]
  filter_upwards [h1, h2, Lp.coeFn_sub (solution Ω u₀ t) (solution Ω v₀ t)] with x hx1 hx2 hx3
  rw [hx3, Pi.sub_apply] at hx1 hx2
  rw [abs_le]
  exact ⟨hx2, hx1⟩

end IsSolution

end Heat

namespace Heat

open LinearPMap LinearPMap.PowDomain SobolevMultiIndex Elliptic

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

namespace IsSolution

variable {u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}

/-- **The solution with a test function as datum is continuous on
$\overline{\Omega} \times [0, \infty)$.** Let $\Omega \subseteq \mathbb{R}^N$ be open with
$N = d + 1$, and let $\ell \in \mathbb{N}$ with $N/2 < 2\ell$. Assume that $\Omega$ is of class
$C^{2\ell}$, that $\partial \Omega$ is bounded, and that $\Omega$ is a $W^{1,q}$-extension
domain for every $q$. Let $\varphi \in \mathcal{D}(\Omega)$ be a test function. Then there is $V
: \mathbb{R}^N \times \mathbb{R} \to \mathbb{R}$, continuous on
$\overline{\Omega} \times [0, \infty)$, such that for every $t \ge 0$ the function $V(\cdot, t)$
equals the solution $u(t)$ with datum $\varphi$ almost everywhere on $\Omega$.

The datum $\varphi$ lies in $D(A^\ell)$ (`testFunction_exists_powDomain`), so
$u \in C([0, \infty); H^{2\ell}(\Omega))$
(`Heat.IsSolution.contDiffOnThrough_sobolev_Ici_of_powDomain`). The representative $V$ comes
from `Bochner.continuousOn_spaceTime_of_contDiffOnThrough`. The class $C^{2\ell}$ is
`IsContDiffChartDomain`, the extension property is `IsSobolevExtensionDomainAll`, and the
solution is `Heat.solution`. -/
theorem exists_continuousOn_spaceTime_of_testFunction {ℓ : ℕ} (hℓ : ((d : ℝ) + 1) / 2 < 2 * ℓ)
    (hΩ : IsContDiffChartDomain (2 * ℓ) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (hext : IsSobolevExtensionDomainAll (d + 1) Ω) (φ : 𝓓(Ω, ℝ)) :
    ∃ V : EuclideanSpace ℝ (Fin (d + 1)) × ℝ → ℝ,
      ContinuousOn V (closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ×ˢ Ici 0) ∧
      ∀ t ∈ Ici (0 : ℝ), (fun x ↦ V (x, t)) =ᵐ[volume.restrict
        (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] solution Ω φ.toL2 t := by
  obtain ⟨x, hx⟩ := testFunction_exists_powDomain φ ℓ
  have hx0 : applyL (dirichletLaplacian Ω) ℓ 0 x = φ.toL2 := by simpa using hx 0
  have hc := (isSolution_solution (Ω := Ω) φ.toL2).contDiffOnThrough_sobolev_Ici_of_powDomain x
    hx0 le_rfl hΩ hΓ
  exact Bochner.continuousOn_spaceTime_of_contDiffOnThrough hext (by push_cast; exact hℓ)
    (hc.of_le (by simp))

/-- **Continuity of the solution on $\overline{Q}$, for a domain of class $C^{2\ell}$.** Let
$\Omega \subseteq \mathbb{R}^N$ be open with $N = d + 1$, and let $\ell \in \mathbb{N}$ with
$N/2 < 2\ell$. Assume that $\Omega$ is of class $C^{2\ell}$ and that $\partial \Omega$ is
bounded. Let $u$ be the solution of the heat equation with datum $u_0 \in L^2(\Omega)$, and
assume that $u_0 = f$ almost everywhere on $\Omega$ for a function $f$ that is continuous on
$\overline{\Omega}$, vanishes on $\partial \Omega$, and tends to $0$ at infinity along $\Omega$.
Then there is $U : \mathbb{R}^N \times \mathbb{R} \to \mathbb{R}$, continuous on $\overline{Q} =
\overline{\Omega} \times [0, \infty)$, such that $U(\cdot, t) = u(t)$ almost everywhere on
$\Omega$ for every $t \ge 0$, and $U(\cdot, 0) = f$ on $\overline{\Omega}$. This is Corollary
10.5 of [brezis2011functional] in a general form.

The condition at infinity is footnote 6 of [brezis2011functional]; it holds automatically when
$\Omega$ is bounded. It is stated as a limit along the filter `cocompact ⊓ 𝓟 Ω`.

The proof follows the source. Test functions $\varphi_n \to f$ uniformly on $\Omega$
(`exists_testFunction_tendsto_of_continuousOn`). The solutions $u_n$ with data $\varphi_n$ have
continuous space-time representatives $V_n$
(`Heat.IsSolution.exists_continuousOn_spaceTime_of_testFunction`, from Theorem 10.2). By the
maximum principle, $|u_n(t) - u_m(t)| \le \sup_\Omega |\varphi_n - \varphi_m|$ almost everywhere
(`Heat.IsSolution.abs_sub_le_of_abs_sub_le`), hence everywhere on $\overline{\Omega}$ by
continuity (`ContinuousOn.abs_le_on_closure_of_ae_abs_le`). So the $V_n$ are uniformly Cauchy on
$\overline{\Omega} \times [0, \infty)$ and converge uniformly to a continuous $U$. For
$t \ge 0$, $|u_n(t) - u(t)| \le \sup_\Omega |\varphi_n - f| \to 0$ almost everywhere, so
$U(\cdot, t) = u(t)$ almost everywhere. The $L^2$ convergence $u_n(t) \to u(t)$ of the source is
not needed, because the semigroup is an $L^\infty$ contraction. -/
theorem continuousOn_spaceTime_of_isContDiffChartDomain (h : IsSolution Ω u₀ u) {ℓ : ℕ}
    (hℓ : ((d : ℝ) + 1) / 2 < 2 * ℓ)
    (hΩ : IsContDiffChartDomain (2 * ℓ) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    {f : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hf : ContinuousOn f (closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (hf0 : ∀ x ∈ frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), f x = 0)
    (hft : Tendsto f (cocompact (EuclideanSpace ℝ (Fin (d + 1))) ⊓
      𝓟 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (𝓝 0))
    (hu₀ : u₀ =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] f) :
    ∃ U : EuclideanSpace ℝ (Fin (d + 1)) × ℝ → ℝ,
      ContinuousOn U (closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ×ˢ Ici 0) ∧
      (∀ t ∈ Ici (0 : ℝ),
        (fun x ↦ U (x, t)) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] u t) ∧
      EqOn (fun x ↦ U (x, 0)) f (closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) := by
  set S : Set (EuclideanSpace ℝ (Fin (d + 1)) × ℝ) :=
    closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ×ˢ Ici 0 with hS
  -- the extension-domain hypothesis
  have h2ℓ : 0 < 2 * ℓ := by
    have : (0 : ℝ) < 2 * ℓ := lt_of_le_of_lt (by positivity) hℓ
    exact_mod_cast this
  have hΩ1 : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) :=
    hΩ.of_le (by exact_mod_cast h2ℓ)
  have hext : IsSobolevExtensionDomainAll (d + 1) Ω :=
    IsSobolevExtensionDomainAll.of_isContDiffChartDomain hΩ1 hΓ
  -- the approximants and their continuous solutions
  obtain ⟨φ, hφ⟩ := exists_testFunction_tendsto_of_continuousOn hf hf0 hft
  choose V hVc hVae using fun n ↦
    exists_continuousOn_spaceTime_of_testFunction hℓ hΩ hΓ hext (φ n)
  -- uniformly Cauchy on `closure Ω × [0, ∞)`
  have hcauchy : UniformCauchySeqOn V atTop S := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.1
      (Metric.tendstoUniformlyOn_iff.1 hφ (ε / 3) (by positivity))
    refine ⟨n₀, fun m hm n hn q hq ↦ ?_⟩
    obtain ⟨x, t⟩ := q
    obtain ⟨hx, ht⟩ : x ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ∧ t ∈ Ici (0 : ℝ) :=
      hq
    have hb : ∀ᵐ y ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
        |(φ m).toL2 y - (φ n).toL2 y| ≤ 2 * ε / 3 := by
      filter_upwards [(φ m).coeFn_toL2, (φ n).coeFn_toL2,
        ae_restrict_mem Ω.isOpen.measurableSet] with y hym hyn hyΩ
      rw [hym, hyn]
      have h1 := hn₀ m hm y hyΩ
      have h2 := hn₀ n hn y hyΩ
      rw [Real.dist_eq] at h1 h2
      calc |φ m y - φ n y| = |(f y - φ n y) - (f y - φ m y)| := by ring_nf
        _ ≤ |f y - φ n y| + |f y - φ m y| := abs_sub _ _
        _ ≤ 2 * ε / 3 := by linarith
    have hae := (isSolution_solution (Ω := Ω) (φ m).toL2).abs_sub_le_of_abs_sub_le
      (isSolution_solution (Ω := Ω) (φ n).toL2) (by positivity) hb ht
    have hVt : ∀ y ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
        |V m (y, t) - V n (y, t)| ≤ 2 * ε / 3 := by
      refine ContinuousOn.abs_le_on_closure_of_ae_abs_le (μ := volume) Ω.isOpen ?_ ?_
      · exact ((hVc m).comp (continuousOn_id.prodMk continuousOn_const) fun y hy ↦ ⟨hy, ht⟩).sub
          ((hVc n).comp (continuousOn_id.prodMk continuousOn_const) fun y hy ↦ ⟨hy, ht⟩)
      · filter_upwards [hae, hVae m t ht, hVae n t ht] with y hy hym hyn
        rw [hym, hyn]
        exact hy
    rw [Real.dist_eq]
    exact (hVt x hx).trans_lt (by linarith)
  -- the uniform limit
  set U : EuclideanSpace ℝ (Fin (d + 1)) × ℝ → ℝ := fun q ↦ limUnder atTop fun n ↦ V n q with hU
  have hUlim : ∀ q ∈ S, Tendsto (fun n ↦ V n q) atTop (𝓝 (U q)) := fun q hq ↦
    (hcauchy.cauchySeq hq).tendsto_limUnder
  have hUnif : TendstoUniformlyOn V U atTop S := hcauchy.tendstoUniformlyOn_of_tendsto hUlim
  have hUc : ContinuousOn U S := hUnif.continuousOn (Eventually.of_forall hVc).frequently
  -- the representative property
  have hUrep : ∀ t ∈ Ici (0 : ℝ),
      (fun x ↦ U (x, t)) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] u t := by
    intro t ht
    have hrate : ∀ k : ℕ, ∃ M : ℕ, ∀ n, M ≤ n →
        ∀ᵐ y ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
          |solution Ω (φ n).toL2 t y - solution Ω u₀ t y| ≤ 1 / (k + 1) := by
      intro k
      obtain ⟨M, hM⟩ := eventually_atTop.1
        (Metric.tendstoUniformlyOn_iff.1 hφ (1 / (k + 1)) (by positivity))
      refine ⟨M, fun n hn ↦ ?_⟩
      refine (isSolution_solution (Ω := Ω) (φ n).toL2).abs_sub_le_of_abs_sub_le
        (isSolution_solution (Ω := Ω) u₀) (by positivity) ?_ ht
      filter_upwards [(φ n).coeFn_toL2, hu₀, ae_restrict_mem Ω.isOpen.measurableSet]
        with y hy hy' hyΩ
      rw [hy, hy', abs_sub_comm, ← Real.dist_eq]
      exact (hM n hn y hyΩ).le
    choose M hM using hrate
    have hae : ∀ᵐ y ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
        y ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ∧
        (∀ n, V n (y, t) = solution Ω (φ n).toL2 t y) ∧
        ∀ k n, M k ≤ n → |solution Ω (φ n).toL2 t y - solution Ω u₀ t y| ≤ 1 / (k + 1) := by
      refine (ae_restrict_mem Ω.isOpen.measurableSet).and
        ((ae_all_iff.2 fun n ↦ hVae n t ht).and (ae_all_iff.2 fun k ↦ ae_all_iff.2 fun n ↦ ?_))
      by_cases hn : M k ≤ n
      · exact (hM k n hn).mono fun y hy _ ↦ hy
      · exact Eventually.of_forall fun y hn' ↦ absurd hn' hn
    rw [h.eqOn_solution ht]
    filter_upwards [hae] with y hy
    obtain ⟨hyΩ, hyV, hyb⟩ := hy
    have h1 : Tendsto (fun n ↦ V n (y, t)) atTop (𝓝 (U (y, t))) :=
      hUlim (y, t) ⟨subset_closure hyΩ, ht⟩
    have h2 : Tendsto (fun n ↦ V n (y, t)) atTop (𝓝 (solution Ω u₀ t y)) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
      exact ⟨M k, fun n hn ↦ by rw [hyV n, Real.dist_eq]; exact (hyb k n hn).trans_lt hk⟩
    exact tendsto_nhds_unique h1 h2
  refine ⟨U, hUc, hUrep, ?_⟩
  -- the initial slice
  have hU0 : ContinuousOn (fun x ↦ U (x, 0))
      (closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    hUc.comp (continuousOn_id.prodMk continuousOn_const) fun x hx ↦ ⟨hx, self_mem_Ici⟩
  have hae0 : (fun x ↦ U (x, 0)) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
      f := by
    have := hUrep 0 self_mem_Ici
    rw [h.apply_zero] at this
    exact this.trans hu₀
  exact (Measure.eqOn_open_of_ae_eq hae0 Ω.isOpen (hU0.mono subset_closure)
    (hf.mono subset_closure)).of_subset_closure hU0 hf subset_closure le_rfl

/-- **Continuity of the solution on $\overline{Q}$.** Let $\Omega \subseteq \mathbb{R}^N$ be open
with $N = d + 1$, of class $C^\infty$, with $\Gamma = \partial \Omega$ bounded. Let $u$ be the
solution of the heat equation with datum $u_0 \in L^2(\Omega)$, and assume that $u_0 = f$ almost
everywhere on $\Omega$ for a function $f \in C(\overline{\Omega})$ with $f = 0$ on $\Gamma$ and
$f(x) \to 0$ as $|x| \to \infty$ in $\Omega$. Then $u \in C(\overline{Q})$: there is $U :
\mathbb{R}^N \times \mathbb{R} \to \mathbb{R}$, continuous on
$\overline{\Omega} \times [0, \infty)$, such that $U(\cdot, t) = u(t)$ almost everywhere on
$\Omega$ for every $t \ge 0$, and $U(\cdot, 0) = f$ on $\overline{\Omega}$. This is Corollary
10.5 of [brezis2011functional].

The condition at infinity is footnote 6 of [brezis2011functional] and is void when $\Omega$ is
bounded. The general form, on a domain of class $C^{2\ell}$ with $N/2 < 2\ell$, is
`Heat.IsSolution.continuousOn_spaceTime_of_isContDiffChartDomain`. -/
theorem continuousOn_spaceTime (h : IsSolution Ω u₀ u)
    (hΩ : IsContDiffChartDomain ∞ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    {f : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hf : ContinuousOn f (closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (hf0 : ∀ x ∈ frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), f x = 0)
    (hft : Tendsto f (cocompact (EuclideanSpace ℝ (Fin (d + 1))) ⊓
      𝓟 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (𝓝 0))
    (hu₀ : u₀ =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] f) :
    ∃ U : EuclideanSpace ℝ (Fin (d + 1)) × ℝ → ℝ,
      ContinuousOn U (closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ×ˢ Ici 0) ∧
      (∀ t ∈ Ici (0 : ℝ),
        (fun x ↦ U (x, t)) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] u t) ∧
      EqOn (fun x ↦ U (x, 0)) f (closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
  h.continuousOn_spaceTime_of_isContDiffChartDomain (ℓ := d + 1)
    (by push_cast; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
    (hΩ.of_le (WithTop.coe_le_coe.2 le_top)) hΓ hf hf0 hft hu₀

/-- **Continuity of the solution on $\overline{Q}$, for a bounded domain.** Let
$\Omega \subseteq \mathbb{R}^N$ be open and bounded with $N = d + 1$, and of class $C^\infty$.
Let $u$ be the solution of the heat equation with datum $u_0 \in L^2(\Omega)$, and assume that
$u_0 = f$ almost everywhere on $\Omega$ for a function $f \in C(\overline{\Omega})$ with $f = 0$
on $\Gamma = \partial \Omega$. Then there is $U : \mathbb{R}^N \times \mathbb{R} \to
\mathbb{R}$, continuous on $\overline{\Omega} \times [0, \infty)$, such that
$U(\cdot, t) = u(t)$ almost everywhere on $\Omega$ for every $t \ge 0$, and $U(\cdot, 0) = f$ on
$\overline{\Omega}$. This is Corollary 10.5 of [brezis2011functional] for a bounded domain, as
the source prints it.

The condition at infinity of `Heat.IsSolution.continuousOn_spaceTime` is void here, because the
filter `cocompact ⊓ 𝓟 Ω` is trivial (`Bornology.IsBounded.tendsto_cocompact_inf_principal`). -/
theorem continuousOn_spaceTime_of_isBounded (h : IsSolution Ω u₀ u)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΩ : IsContDiffChartDomain ∞ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    {f : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hf : ContinuousOn f (closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (hf0 : ∀ x ∈ frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), f x = 0)
    (hu₀ : u₀ =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] f) :
    ∃ U : EuclideanSpace ℝ (Fin (d + 1)) × ℝ → ℝ,
      ContinuousOn U (closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ×ˢ Ici 0) ∧
      (∀ t ∈ Ici (0 : ℝ),
        (fun x ↦ U (x, t)) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] u t) ∧
      EqOn (fun x ↦ U (x, 0)) f (closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
  h.continuousOn_spaceTime hΩ (hb.isCompact_closure.isBounded.subset frontier_subset_closure)
    hf hf0 (hb.tendsto_cocompact_inf_principal f 0) hu₀

end IsSolution

end Heat
