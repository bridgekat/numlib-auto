/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Sobolev.Friedrichs
import Numlib.Analysis.Sobolev.Translate
import Numlib.Analysis.Sobolev.Zero

/-!
# The translation curve in $L^p$ and its derivatives

For $a \in E$ and a function $f$ on $E$, write $\tau_a f = f(\cdot + a)$. For
$f \in L^p(\mathbb{R}^N)$ with $p < \infty$ and a direction $y$, the **translation curve**
$t \mapsto \tau_{ty} f$ is continuous into $L^p$. For $u \in W^{1,p}(\mathbb{R}^N)$ and the standard
basis vector $e_i$, the curve $t \mapsto \tau_{t e_i} u$ is differentiable in $L^p$ with derivative
$\tau_{t e_i} \partial_i u$: this is the strong derivative of the translation group along $e_i$. By
induction, the curve is $C^k$ into $L^p$ for $u \in W^{k,p}(\mathbb{R}^N)$, and it is $C^1$ into
$W^{1,p}(\mathbb{R}^N)$ for $u \in W^{2,p}(\mathbb{R}^N)$. This is the calculus behind d'Alembert's
formula $\frac12 (u_0(x + t) + u_0(x - t)) + \frac12 \int_{x-t}^{x+t} v_0$ for the wave equation on
$\mathbb{R}$ ([brezis2011functional], §10.3, Remark 8).

The module also studies the **primitive curve** $t \mapsto \int_{-t}^{t} \tau_{sy} f \, ds$, a
Bochner integral in $L^p$. It is the $L^p$ class of $x \mapsto \int_{-t}^{t} f(x + sy) \, ds$, it is
a $C^1$ curve with derivative $\tau_{ty} f + \tau_{-ty} f$, and for $u \in W^{1,p}(\mathbb{R}^N)$
the primitive curve of $\partial_i u$ along $e_i$ is $\tau_{t e_i} u - \tau_{-t e_i} u$.

## Main definitions

* `MeasureTheory.Lp.translateCurve`: the translation curve $t \mapsto \tau_{ty} f$ of a function
  $f \in L^p(E)$.
* `MeasureTheory.Lp.primitiveCurve`: the primitive curve $t \mapsto \int_0^t (\tau_{sy} f +
  \tau_{-sy} f) \, ds$ in $L^p(E)$.
* `SobolevEuclidean.primitiveCurveL`: the same primitive curve in $W^{k,p}(\mathbb{R}^N)$.

## Main results

* `MeasureTheory.Lp.continuous_translateCurve`: for $p < \infty$ the translation curve is continuous
  into $L^p$.
* `SobolevEuclidean.norm_translate_fnL_sub_le`: $\|\tau_a u - u\|_p \le N \|a\| \|u\|_{W^{1,p}}$ for
  $u \in W^{1,p}(\mathbb{R}^N)$ and $p < \infty$.
* `SobolevEuclidean.hasDerivAt_translateCurve_fnL`: for $u \in W^{1,p}(\mathbb{R}^N)$ and
  $p < \infty$, the curve $t \mapsto \tau_{t e_i} u$ has the derivative $\tau_{t e_i} \partial_i u$
  in $L^p$.
* `SobolevEuclidean.contDiff_translateCurve_fnL`: for $u \in W^{k,p}(\mathbb{R}^N)$ and
  $p < \infty$, the curve $t \mapsto \tau_{t e_i} u$ is $C^k$ into $L^p$.
* `SobolevEuclidean.contDiff_translateL`: for $u \in W^{2,p}(\mathbb{R}^N)$ and $p < \infty$, the
  curve $t \mapsto \tau_{t e_i} u$ is $C^1$ into $W^{1,p}(\mathbb{R}^N)$.
* `MeasureTheory.Lp.coeFn_primitiveCurve`: in $L^2$, the primitive curve is the class of $x \mapsto
  \int_0^t (f(x + sy) + f(x - sy)) \, ds$.
* `MeasureTheory.Lp.hasDerivAt_primitiveCurve`: the primitive curve has the derivative
  $\tau_{ty} f + \tau_{-ty} f$.
* `SobolevEuclidean.primitiveCurve_weakDeriv_single`: the primitive curve of $\partial_i u$ along
  $e_i$ is $\tau_{t e_i} u - \tau_{-t e_i} u$.

## Proof outline

At $t = 0$, the remainder $\tau_{h e_i} u - u - h \partial_i u$ is estimated through a test function
$v$ close to $u$ in $W^{1,p}(\mathbb{R}^N)$, which exists because test functions are dense in
$W^{1,p}(\mathbb{R}^N)$. Three terms appear. The first is the translation estimate $\|\tau_{h
e_i}(u - v) - (u - v)\|_p \le N |h| \|u - v\|_{W^{1,p}}$ of Proposition 9.3 of
[brezis2011functional]. The second is the Taylor bound $\|\tau_{h e_i} v - v - h \partial_i v\|_p
\le C h^2$ for a $C^2$ function with compact support, which follows from the Lipschitz continuity of
its derivative. The third is $|h| \|\partial_i v - \partial_i u\|_p \le |h| \|u - v\|_{W^{1,p}}$. At
a general $t$, the group law $\tau_{(s + t) e_i} = \tau_{s e_i} \circ \tau_{t e_i}$ and the isometry
$\tau_{t e_i}$ reduce the claim to $t = 0$. The identification of the primitive curve uses Fubini's
theorem against indicator functions of sets of finite measure.

## Implementation notes

* The space $L^p$ of the whole space is `Lp F p (μ.restrict ↑⊤)` with `⊤ : Opens E`. This is the
  form in which `Numlib.Analysis.PDE.DirichletLaplacian` and `Numlib.Analysis.PDE.Wave` read
  $L^2(\Omega)$. The space $W^{k,p}(\mathbb{R}^N)$ is `SobolevEuclidean N k p ⊤`.
* The translations are `MeasureTheory.Lp.translate` and `SobolevMultiIndex.translateL` of
  `Numlib.Analysis.Sobolev.Translate`. The whole space is invariant under every translation by
  `IsTranslationInvariant.top`.
* The function $u \in L^p$ of an element of $W^{k,p}$ is `SobolevMultiIndex.fnL`, and $\partial_i u$
  is `SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i)`. The vector $e_i$ is
  `EuclideanSpace.single i 1`.
* The general lemmas `HasDerivAt.of_submodule_val`, `hasDerivAt_piLp` and
  `SobolevMultiIndex.hasDerivAt_of_forall_weakDeriv` read a derivative in $W^{k,p}(\Omega)$ off the
  derivatives of the components in $L^p(\Omega)$.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal NNReal Topology InnerProductSpace

noncomputable section

/-! ### Derivatives and continuity into submodules and $\ell^p$ products -/

section Subtype

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] {S : Submodule ℝ M}

/-- Let $S$ be a submodule of a real normed space $M$, and let $f : \mathbb{R} \to S$. If the curve
$s \mapsto f(s)$, read in $M$, has the derivative $f'$ at $t$, then $f$ has the derivative $f'$
at $t$ in $S$ with the subspace topology. -/
theorem HasDerivAt.of_submodule_val {f : ℝ → S} {f' : S} {t : ℝ}
    (h : HasDerivAt (fun s ↦ (f s : M)) (f' : M) t) : HasDerivAt f f' t := by
  rw [hasDerivAt_iff_tendsto_slope] at h ⊢
  rw [tendsto_subtype_rng]
  refine h.congr fun s ↦ ?_
  simp only [slope, vsub_eq_sub, Submodule.coe_smul, Submodule.coe_sub]

/-- Let $S$ be a submodule of a real normed space $M$. A curve $f : \mathbb{R} \to S$ is continuous
if the curve $s \mapsto f(s)$, read in $M$, is continuous. -/
theorem Continuous.of_submodule_val {f : ℝ → S} (h : Continuous fun s ↦ (f s : M)) :
    Continuous f :=
  continuous_induced_rng.2 h

end Subtype

section PiLp

variable {ι : Type*} [Fintype ι] {p : ℝ≥0∞} [Fact (1 ≤ p)] {β : ι → Type*}
  [∀ i, NormedAddCommGroup (β i)] [∀ i, NormedSpace ℝ (β i)]

-- The normed structure of `PiLp p β` needs `Fintype ι`, which the linter does not see.
set_option linter.unusedFintypeInType false in
/-- Let $\prod_i \beta_i$ be a finite product of real normed spaces with the $\ell^p$ norm,
$p \ge 1$. A curve $f$ in this product has the derivative $f'$ at $t$ if each component
$s \mapsto f(s)_i$ has the derivative $f'_i$ at $t$. -/
theorem hasDerivAt_piLp {f : ℝ → PiLp p β} {f' : PiLp p β} {t : ℝ}
    (h : ∀ i, HasDerivAt (fun s ↦ f s i) (f' i) t) : HasDerivAt f f' t := by
  rw [hasDerivAt_iff_hasFDerivAt, ← (PiLp.continuousLinearEquiv p ℝ β).comp_hasFDerivAt_iff]
  exact hasFDerivAt_pi.2 fun i ↦ hasDerivAt_iff_hasFDerivAt.1 (h i)

omit [Fintype ι] [Fact (1 ≤ p)] [∀ i, NormedSpace ℝ (β i)] in
/-- A curve $f$ in an $\ell^p$ product of normed groups is continuous if each component
$s \mapsto f(s)_i$ is continuous. -/
theorem continuous_piLp {f : ℝ → PiLp p β} (h : ∀ i, Continuous fun s ↦ f s i) :
    Continuous f :=
  continuous_induced_rng.2 (continuous_pi h)

end PiLp

section Sobolev

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ} {p : ℝ≥0∞}
  {Ω : Opens E} {μ : Measure E}

namespace SobolevMultiIndex

/-- For $u, v \in W^{k,p}(\Omega)$ and a multi-index $\alpha$ with $|\alpha| \le k$,
$\partial^\alpha (u - v) = \partial^\alpha u - \partial^\alpha v$. -/
theorem weakDeriv_sub (u v : SobolevMultiIndex F b k p Ω μ) (α : MultiIndexLE ι k) :
    weakDeriv (u - v) α = weakDeriv u α - weakDeriv v α :=
  rfl

/-- For $u \in W^{k,p}(\Omega)$ and a multi-index $\alpha$ with $|\alpha| \le k$,
$\partial^\alpha (-u) = -\partial^\alpha u$. -/
theorem weakDeriv_neg (u : SobolevMultiIndex F b k p Ω μ) (α : MultiIndexLE ι k) :
    weakDeriv (-u) α = -weakDeriv u α :=
  rfl

variable [Fact (1 ≤ p)]

/-- Let $p \ge 1$ and $u, v \in W^{k,p}(\Omega)$. The function in $L^p(\Omega)$ of $u - v$ is the
difference of the functions of $u$ and $v$. -/
theorem fnL_sub (u v : SobolevMultiIndex F b k p Ω μ) :
    fnL F b k p Ω μ (u - v) = fnL F b k p Ω μ u - fnL F b k p Ω μ v :=
  rfl

/-- Let $p \ge 1$ and $u, v \in W^{k,p}(\Omega)$. The function in $L^p(\Omega)$ of $u + v$ is the
sum of the functions of $u$ and $v$. -/
theorem fnL_add (u v : SobolevMultiIndex F b k p Ω μ) :
    fnL F b k p Ω μ (u + v) = fnL F b k p Ω μ u + fnL F b k p Ω μ v :=
  rfl

/-- Let $p \ge 1$ and $u, v \in W^{k,p}(\Omega)$. For $c \in \mathbb{R}$, the function in
$L^p(\Omega)$ of $c u$ is $c$ times the function of $u$. -/
theorem fnL_smul (c : ℝ) (u : SobolevMultiIndex F b k p Ω μ) :
    fnL F b k p Ω μ (c • u) = c • fnL F b k p Ω μ u :=
  rfl

/-- Let $p \ge 1$ and let $f : \mathbb{R} \to W^{k,p}(\Omega)$ and $f' \in W^{k,p}(\Omega)$. If for
every multi-index $\alpha$ with $|\alpha| \le k$ the curve $s \mapsto \partial^\alpha f(s)$ has
the derivative $\partial^\alpha f'$ at $t$ in $L^p(\Omega)$, then $f$ has the derivative $f'$ at
$t$ in $W^{k,p}(\Omega)$.

The proof combines `hasDerivAt_piLp` and `HasDerivAt.of_submodule_val`, since $W^{k,p}(\Omega)$
is a submodule of an $\ell^p$ product of copies of $L^p(\Omega)$. -/
theorem hasDerivAt_of_forall_weakDeriv {f : ℝ → SobolevMultiIndex F b k p Ω μ}
    {f' : SobolevMultiIndex F b k p Ω μ} {t : ℝ}
    (h : ∀ α, HasDerivAt (fun s ↦ weakDeriv (f s) α) (weakDeriv f' α) t) :
    HasDerivAt f f' t :=
  HasDerivAt.of_submodule_val (hasDerivAt_piLp h)

/-- Let $p \ge 1$. A curve $f : \mathbb{R} \to W^{k,p}(\Omega)$ is continuous if for every
multi-index $\alpha$ with $|\alpha| \le k$ the curve $s \mapsto \partial^\alpha f(s)$ is
continuous into $L^p(\Omega)$. -/
theorem continuous_of_forall_weakDeriv {f : ℝ → SobolevMultiIndex F b k p Ω μ}
    (h : ∀ α, Continuous fun s ↦ weakDeriv (f s) α) : Continuous f :=
  Continuous.of_submodule_val (continuous_piLp h)

end SobolevMultiIndex

end Sobolev

/-! ### The second-order Taylor bound in $L^p$ for a $C^2$ function with compact support -/

section Smooth

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **Second-order Taylor bound with a Lipschitz derivative.** Let $g : E \to F$ be differentiable,
and let its derivative $g'$ be $L$-Lipschitz. Then for all $x, v \in E$,
$$\|g(x + v) - g(x) - g'(x) v\| \le L \|v\|^2.$$

The proof applies the mean value inequality on the ball of radius $\|v\|$ about $x$. -/
theorem norm_sub_sub_fderiv_le_of_lipschitzWith {g : E → F} {L : ℝ≥0}
    (hg : Differentiable ℝ g) (hL : LipschitzWith L (fderiv ℝ g)) (x v : E) :
    ‖g (x + v) - g x - fderiv ℝ g x v‖ ≤ L * ‖v‖ ^ 2 := by
  have key := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' (f := g) (f' := fderiv ℝ g)
    (φ := fderiv ℝ g x) (C := L * ‖v‖) (s := closedBall x ‖v‖) (x := x) (y := x + v)
    (fun z _ ↦ (hg z).hasFDerivAt.hasFDerivWithinAt) (fun z hz ↦ ?_) (convex_closedBall _ _)
    (mem_closedBall_self (norm_nonneg _)) (by simp [mem_closedBall, dist_eq_norm])
  · rw [add_sub_cancel_left] at key
    calc ‖g (x + v) - g x - fderiv ℝ g x v‖ ≤ L * ‖v‖ * ‖v‖ := key
      _ = L * ‖v‖ ^ 2 := by ring
  · calc ‖fderiv ℝ g z - fderiv ℝ g x‖ = dist (fderiv ℝ g z) (fderiv ℝ g x) :=
          (dist_eq_norm _ _).symm
      _ ≤ L * dist z x := hL.dist_le_mul z x
      _ ≤ L * ‖v‖ := by gcongr; exact mem_closedBall.1 hz

variable [MeasurableSpace E] [BorelSpace E] [ProperSpace E] {μ : Measure E}
  [IsFiniteMeasureOnCompacts μ]

/-- Let $E$ be a proper space with a Borel measure $\mu$ that is finite on compact sets, and let
$g : E \to F$ be a $C^2$ function with compact support. Then for every direction $y \in E$ and
every exponent $p$ there is a constant $C \ge 0$ such that for all $h$ with $|h| \le 1$,
$$\|g(\cdot + h y) - g - h \, g'(\cdot) y\|_{L^p(\mu)} \le C h^2.$$

The proof gives $C = \mu(K)^{1/p} L \|y\|^2$, where $L$ is a Lipschitz constant of $g'$ and $K$
is the closed $\|y\|$-neighbourhood of the support of $g$. -/
theorem ContDiff.exists_eLpNorm_sub_sub_smul_fderiv_le {g : E → F} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (y : E) (p : ℝ≥0∞) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, |h| ≤ 1 →
      eLpNorm (fun x ↦ g (x + h • y) - g x - h • fderiv ℝ g x y) p μ
        ≤ ENNReal.ofReal (C * h ^ 2) := by
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (hgc.fderiv ℝ)
    (hg.fderiv_right (m := 1) (by norm_num)) one_ne_zero
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  set K : Set E := cthickening ‖y‖ (tsupport g) with hK
  have hKc : IsCompact K := hgc.cthickening
  have hKμ : μ K ≠ ⊤ := hKc.measure_lt_top.ne
  refine ⟨(μ K).toReal ^ p.toReal⁻¹ * (L * ‖y‖ ^ 2), by positivity, fun h hh ↦ ?_⟩
  set G : E → F := fun x ↦ g (x + h • y) - g x - h • fderiv ℝ g x y with hG
  have hGm : AEStronglyMeasurable G μ := by
    refine Continuous.aestronglyMeasurable ?_
    have h1 : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
    exact ((hg.continuous.comp (continuous_id.add continuous_const)).sub hg.continuous).sub
      ((h1.clm_apply continuous_const).const_smul h)
  -- the pointwise bound
  have hpt : ∀ x, ‖G x‖ ≤ L * ‖y‖ ^ 2 * h ^ 2 := fun x ↦ by
    have := norm_sub_sub_fderiv_le_of_lipschitzWith hgd hL x (h • y)
    rw [map_smul] at this
    calc ‖G x‖ = ‖g (x + h • y) - g x - h • fderiv ℝ g x y‖ := rfl
      _ ≤ L * ‖h • y‖ ^ 2 := this
      _ = L * ‖y‖ ^ 2 * h ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]; ring
  -- the support
  have hsupp : Function.support G ⊆ K := by
    intro x hx
    by_contra hxK
    apply hx
    have hx1 : x ∉ tsupport g := fun h' ↦ hxK (self_subset_cthickening _ h')
    have hx2 : x + h • y ∉ tsupport g := fun h' ↦ hxK (by
      refine mem_cthickening_of_dist_le x (x + h • y) ‖y‖ _ h' ?_
      rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs]
      calc |h| * ‖y‖ ≤ 1 * ‖y‖ := by gcongr
        _ = ‖y‖ := one_mul _)
    have hx3 : fderiv ℝ g x = 0 :=
      image_eq_zero_of_notMem_tsupport fun h' ↦ hx1 (tsupport_fderiv_subset ℝ h')
    simp only [hG, image_eq_zero_of_notMem_tsupport hx1, image_eq_zero_of_notMem_tsupport hx2,
      hx3, zero_apply, smul_zero, sub_zero]
  calc eLpNorm G p μ = eLpNorm G p (μ.restrict K) :=
        (eLpNorm_restrict_eq_of_support_subset hGm hsupp).symm
    _ ≤ (μ.restrict K) univ ^ p.toReal⁻¹ * ENNReal.ofReal (L * ‖y‖ ^ 2 * h ^ 2) :=
        eLpNorm_le_of_ae_bound hGm.restrict (Eventually.of_forall hpt)
    _ = ENNReal.ofReal ((μ K).toReal ^ p.toReal⁻¹ * (L * ‖y‖ ^ 2) * h ^ 2) := by
        have e : μ K ^ p.toReal⁻¹ = ENNReal.ofReal ((μ K).toReal ^ p.toReal⁻¹) := by
          rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg
            (inv_nonneg.2 ENNReal.toReal_nonneg), ENNReal.ofReal_toReal hKμ]
        rw [Measure.restrict_apply_univ, e, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

end Smooth

/-! ### The translation curve in $L^p$ of the whole space -/

/-- The whole space is invariant under the translation by any $h$. -/
theorem IsTranslationInvariant.top {E : Type*} [AddGroup E] [TopologicalSpace E] (h : E) :
    IsTranslationInvariant ((⊤ : Opens E) : Set E) h := fun _ ↦ Iff.rfl

section Curve

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace MeasureTheory.Lp

variable (F p) in
/-- **The translation curve** of $f \in L^p(E)$ along the direction $y \in E$: the curve
$t \mapsto \tau_{ty} f = f(\cdot + t y)$ in $L^p(E)$. Here $\mu$ is an additive Haar measure on
$E$ and $p \ge 1$.

The space $L^p(E)$ is `Lp F p (μ.restrict ↑⊤)`. The translation by $t y$ is
`MeasureTheory.Lp.translate`. -/
def translateCurve (y : E) (f : Lp F p (μ.restrict ((⊤ : Opens E) : Set E))) (t : ℝ) :
    Lp F p (μ.restrict ((⊤ : Opens E) : Set E)) :=
  translate F p (IsTranslationInvariant.top (t • y)) f

variable (y : E) (f g : Lp F p (μ.restrict ((⊤ : Opens E) : Set E)))

/-- For every $t$, $\tau_{ty} f$ agrees almost everywhere with $x \mapsto f(x + t y)$. -/
theorem coeFn_translateCurve (t : ℝ) :
    translateCurve F p y f t =ᵐ[μ.restrict ((⊤ : Opens E) : Set E)] fun x ↦ f (x + t • y) :=
  coeFn_translate _ f

/-- At $t = 0$ the translation curve is $f$: $\tau_0 f = f$. -/
theorem translateCurve_zero : translateCurve F p y f 0 = f :=
  Lp.ext ((coeFn_translateCurve y f 0).trans (Eventually.of_forall fun x ↦ by simp))

/-- **The group law.** For all $s, t \in \mathbb{R}$,
$\tau_{(s + t) y} f = \tau_{sy} (\tau_{ty} f)$. -/
theorem translateCurve_add (s t : ℝ) :
    translateCurve F p y f (s + t)
      = translate F p (IsTranslationInvariant.top (s • y)) (translateCurve F p y f t) := by
  refine Lp.ext ((coeFn_translateCurve y f (s + t)).trans ?_)
  filter_upwards [coeFn_translate (IsTranslationInvariant.top (s • y)) (translateCurve F p y f t),
    (IsTranslationInvariant.top (s • y)).measurePreserving.quasiMeasurePreserving.ae_eq_comp
      (coeFn_translateCurve y f t)] with x hx hx'
  rw [hx]
  simp only [Function.comp_apply] at hx'
  rw [hx', add_assoc, add_smul, add_comm (s • y)]

/-- The translations are isometries: $\|\tau_{ty} f\|_p = \|f\|_p$ for every $t$. -/
theorem norm_translateCurve (t : ℝ) : ‖translateCurve F p y f t‖ = ‖f‖ :=
  LinearIsometry.norm_map _ f

/-- The translation curve is additive in the function:
$\tau_{ty}(f + g) = \tau_{ty} f + \tau_{ty} g$. -/
theorem translateCurve_add_fun (t : ℝ) :
    translateCurve F p y (f + g) t = translateCurve F p y f t + translateCurve F p y g t :=
  map_add _ f g

/-- The translation curve of a difference: $\tau_{ty}(f - g) = \tau_{ty} f - \tau_{ty} g$. -/
theorem translateCurve_sub_fun (t : ℝ) :
    translateCurve F p y (f - g) t = translateCurve F p y f t - translateCurve F p y g t :=
  map_sub _ f g

/-- The translation curve of a scalar multiple: $\tau_{ty}(c f) = c \, \tau_{ty} f$ for
$c \in \mathbb{R}$. -/
theorem translateCurve_smul_fun (c : ℝ) (t : ℝ) :
    translateCurve F p y (c • f) t = c • translateCurve F p y f t :=
  map_smul _ c f

/-- The translation curve of a negative: $\tau_{ty}(-f) = -\tau_{ty} f$. -/
theorem translateCurve_neg_fun (t : ℝ) :
    translateCurve F p y (-f) t = -translateCurve F p y f t :=
  map_neg _ f

/-- **Strong continuity of the translation group on $L^p$.** Let $E$ be finite-dimensional and let
$p < \infty$. Then for every $f \in L^p(E)$ and every direction $y$, the curve
$t \mapsto \tau_{ty} f$ is continuous into $L^p(E)$.

The proof uses `Continuous.compMeasurePreservingLp` of Mathlib. -/
theorem continuous_translateCurve [FiniteDimensional ℝ E] (hp : p ≠ ⊤) :
    Continuous (translateCurve F p y f) := by
  let Φ : C(ℝ × E, E) := ⟨fun z ↦ z.2 + z.1 • y, by fun_prop⟩
  exact Continuous.compMeasurePreservingLp (f := fun _ ↦ f) (g := fun t ↦ Φ.curry t)
    continuous_const Φ.curry.continuous
    (fun t ↦ (IsTranslationInvariant.top (t • y)).measurePreserving) hp

end MeasureTheory.Lp

end Curve

/-! ### The derivative of the translation curve of a Sobolev function -/

section Deriv

variable {N : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

local notation "𝔼" => EuclideanSpace ℝ (Fin N)
local notation "𝔟" => OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin N) ℝ)

open SobolevMultiIndex MeasureTheory.Lp

/-- Let $p \ge 1$ and $u \in W^{k+1,p}(\Omega)$. The function of the partial derivative
$\partial_i u \in W^{k,p}(\Omega)$ is the component of $u$ at the multi-index $e_i$, as elements
of $L^p(\Omega)$.

The partial derivative is `SobolevMultiIndex.partialDerivL`, and the multi-index $e_i$ of order
at most $k + 1$ is `MultiIndexLE.singleLE i`. -/
theorem SobolevMultiIndex.fnL_partialDerivL {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {Ω : Opens E} {μ : Measure E} (i : ι) (u : SobolevMultiIndex F b (k + 1) p Ω μ) :
    fnL F b k p Ω μ (partialDerivL F b p Ω μ i u) = weakDeriv u (MultiIndexLE.singleLE i) := by
  change weakDeriv u (MultiIndexLE.addSingle i 0) = _
  rw [MultiIndexLE.addSingle_zero]

/-- Let $p \ge 1$ and $u \in W^{k+1,p}(\Omega)$. When $u$ is read in $W^{1,p}(\Omega)$, its
component at the multi-index $e_i$ is the component of $u$ at $e_i$.

The inclusion $W^{k+1,p}(\Omega) \to W^{1,p}(\Omega)$ is `SobolevMultiIndex.toLowerOrderL`. -/
theorem SobolevMultiIndex.weakDeriv_toLowerOrderL_single {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens E} {μ : Measure E} (i : ι)
    (u : SobolevMultiIndex F b (k + 1) p Ω μ) :
    weakDeriv (toLowerOrderL F b p Ω μ (by omega : 1 ≤ k + 1) u) (MultiIndexLE.single i)
      = weakDeriv u (MultiIndexLE.singleLE i) :=
  rfl

/-- Let $p \ge 1$, $k' \le k$ and $u \in W^{k,p}(\Omega)$. When $u$ is read in $W^{k',p}(\Omega)$,
its function in $L^p(\Omega)$ is unchanged. -/
theorem SobolevMultiIndex.fnL_toLowerOrderL {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k k' : ℕ}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens E} {μ : Measure E} (hk : k' ≤ k)
    (u : SobolevMultiIndex F b k p Ω μ) :
    fnL F b k' p Ω μ (toLowerOrderL F b p Ω μ hk u) = fnL F b k p Ω μ u :=
  rfl

namespace SobolevEuclidean

/-- **The translation estimate in the $L^p$ norm.** Let $p < \infty$, $u \in W^{1,p}(\mathbb{R}^N)$
and $a \in \mathbb{R}^N$. Then
$$\|\tau_a u - u\|_{L^p} \le N \|a\| \, \|u\|_{W^{1,p}}.$$

This is the implication (i) ⇒ (iii) of Proposition 9.3 of [brezis2011functional], obtained from
`SobolevEuclidean.eLpNorm_fn_sub_translate_le_gradNorm`. -/
theorem norm_translate_fnL_sub_le (hp : p ≠ ⊤) (u : SobolevEuclidean N 1 p ⊤) (a : 𝔼) :
    ‖Lp.translate ℝ p (IsTranslationInvariant.top a) (fnL ℝ 𝔟 1 p ⊤ volume u)
      - fnL ℝ 𝔟 1 p ⊤ volume u‖ ≤ N * ‖a‖ * ‖u‖ := by
  rw [Lp.norm_def]
  have h1 : eLpNorm (⇑(Lp.translate ℝ p (IsTranslationInvariant.top a)
        (fnL ℝ 𝔟 1 p ⊤ volume u) - fnL ℝ 𝔟 1 p ⊤ volume u)) p
        (volume.restrict ((⊤ : Opens 𝔼) : Set 𝔼))
      = eLpNorm (fun x ↦ fn u (x + a) - fn u x) p (volume.restrict ((⊤ : Opens 𝔼) : Set 𝔼)) := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [Lp.coeFn_translate (IsTranslationInvariant.top a) (fnL ℝ 𝔟 1 p ⊤ volume u),
      Lp.coeFn_sub (Lp.translate ℝ p (IsTranslationInvariant.top a) (fnL ℝ 𝔟 1 p ⊤ volume u))
        (fnL ℝ 𝔟 1 p ⊤ volume u)] with x hx hx'
    rw [hx', Pi.sub_apply, hx, fnL_apply]
  rw [h1]
  have h4 : eLpNorm (fun x ↦ fn u (x + a) - fn u x) p (volume.restrict ((⊤ : Opens 𝔼) : Set 𝔼))
      ≤ N * ‖a‖ₑ * ENNReal.ofReal (gradNorm u) := by
    rw [Measure.restrict_coe_top]
    exact SobolevEuclidean.eLpNorm_fn_sub_translate_le_gradNorm hp u a
  refine (ENNReal.toReal_mono ?_ h4).trans ?_
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (by simp)) ENNReal.ofReal_ne_top
  · rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast, toReal_enorm,
      ENNReal.toReal_ofReal (gradNorm_nonneg u)]
    gcongr
    exact gradNorm_le_norm u

/-- **Test functions are dense in $W^{1,p}(\mathbb{R}^N)$.** Let $p < \infty$ and
$u \in W^{1,p}(\mathbb{R}^N)$. For every $\delta > 0$ there is an element $v$ of
`SobolevMultiIndex.testFunctions` with $\|u - v\|_{W^{1,p}} < \delta$.

This is the metric form of `SobolevEuclideanZero.eq_top`, which is Remark 17 of chapter 9 of
[brezis2011functional]. -/
theorem exists_testFunctions_norm_sub_lt (hp : p ≠ ⊤) (u : SobolevEuclidean N 1 p ⊤) {δ : ℝ}
    (hδ : 0 < δ) : ∃ v ∈ testFunctions ℝ 𝔟 1 p ⊤ volume, ‖u - v‖ < δ := by
  have hu : u ∈ closure (testFunctions ℝ 𝔟 1 p ⊤ volume : Set (SobolevEuclidean N 1 p ⊤)) := by
    have h : u ∈ SobolevEuclideanZero N 1 p ⊤ := by
      rw [SobolevEuclideanZero.eq_top hp]
      exact Submodule.mem_top
    rw [← Submodule.topologicalClosure_coe]
    exact h
  obtain ⟨v, hv, huv⟩ := Metric.mem_closure_iff.1 hu δ hδ
  exact ⟨v, hv, by rwa [_root_.dist_eq_norm] at huv⟩

/-- Let $v \in W^{1,p}(\mathbb{R}^N)$ be the class of a test function. Then there is a constant
$C \ge 0$ such that for all $h$ with $|h| \le 1$,
$$\|\tau_{h e_i} v - v - h \, \partial_i v\|_{L^p} \le C h^2.$$

This is `ContDiff.exists_eLpNorm_sub_sub_smul_fderiv_le` read on the $L^p$ classes. -/
theorem exists_norm_translateCurve_sub_sub_smul_le {v : SobolevEuclidean N 1 p ⊤}
    (hv : v ∈ testFunctions ℝ 𝔟 1 p ⊤ volume) (i : Fin N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, |h| ≤ 1 →
      ‖translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ)) (fnL ℝ 𝔟 1 p ⊤ volume v) h
        - fnL ℝ 𝔟 1 p ⊤ volume v - h • weakDeriv v (MultiIndexLE.single i)‖ ≤ C * h ^ 2 := by
  obtain ⟨φ, hφ⟩ := hv
  obtain ⟨C, hC0, hC⟩ := (φ.contDiff.of_le (by simp)).exists_eLpNorm_sub_sub_smul_fderiv_le
    (μ := volume.restrict ((⊤ : Opens 𝔼) : Set 𝔼)) φ.hasCompactSupport
    (EuclideanSpace.single i (1 : ℝ)) p
  refine ⟨C, hC0, fun h hh ↦ ?_⟩
  rw [Lp.norm_def]
  have hae : ⇑(translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ)) (fnL ℝ 𝔟 1 p ⊤ volume v) h
      - fnL ℝ 𝔟 1 p ⊤ volume v - h • weakDeriv v (MultiIndexLE.single i))
      =ᵐ[volume.restrict ((⊤ : Opens 𝔼) : Set 𝔼)]
      fun x ↦ φ (x + h • EuclideanSpace.single i (1 : ℝ)) - φ x
        - h • fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) := by
    have hd := SobolevMultiIndexZero.weakDeriv_single_ae_eq_testFunction hφ i
    rw [EuclideanSpace.basisFun_toBasis_apply] at hd
    filter_upwards [Lp.coeFn_sub (translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ))
        (fnL ℝ 𝔟 1 p ⊤ volume v) h - fnL ℝ 𝔟 1 p ⊤ volume v)
        (h • weakDeriv v (MultiIndexLE.single i)),
      Lp.coeFn_sub (translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ))
        (fnL ℝ 𝔟 1 p ⊤ volume v) h) (fnL ℝ 𝔟 1 p ⊤ volume v),
      Lp.coeFn_smul h (weakDeriv v (MultiIndexLE.single i)),
      coeFn_translateCurve (EuclideanSpace.single i (1 : ℝ)) (fnL ℝ 𝔟 1 p ⊤ volume v) h,
      (IsTranslationInvariant.top (h • EuclideanSpace.single i (1 : ℝ))).measurePreserving
        |>.quasiMeasurePreserving.ae_eq_comp hφ, hφ, hd] with x h1 h2 h3 h4 h5 h6 h7
    simp only [Function.comp_apply] at h5
    rw [h1, Pi.sub_apply, h2, Pi.sub_apply, h3, Pi.smul_apply, h4, fnL_apply, h5, h6, h7]
  rw [eLpNorm_congr_ae hae]
  refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hC h hh)).trans ?_
  rw [ENNReal.toReal_ofReal (by positivity)]

/-- Let $p < \infty$, $w \in W^{1,p}(\mathbb{R}^N)$, and let $f \in L^p$ be the function of $w$.
Then for every $t$,
$$\|\tau_{t e_i} f - f\|_{L^p} \le N |t| \, \|w\|_{W^{1,p}}.$$
-/
theorem norm_translateCurve_sub_le (hp : p ≠ ⊤) (w : SobolevEuclidean N 1 p ⊤) (i : Fin N)
    {f : Lp ℝ p (volume.restrict ((⊤ : Opens 𝔼) : Set 𝔼))} (hf : f = fnL ℝ 𝔟 1 p ⊤ volume w)
    (t : ℝ) :
    ‖translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ)) f t - f‖ ≤ N * |t| * ‖w‖ := by
  subst hf
  have h := norm_translate_fnL_sub_le hp w (t • EuclideanSpace.single i (1 : ℝ))
  have e : ‖t • EuclideanSpace.single i (1 : ℝ)‖ = |t| := by
    rw [norm_smul, Real.norm_eq_abs, PiLp.norm_single, norm_one, mul_one]
  rw [e] at h
  exact h

/-- Let $w \in W^{1,p}(\mathbb{R}^N)$ and let $\alpha$ be a multi-index with $|\alpha| \le 1$. Then
$\|\partial^\alpha w\|_{L^p} \le \|w\|_{W^{1,p}}$. -/
theorem norm_le_of_eq_weakDeriv (w : SobolevEuclidean N 1 p ⊤) {α : MultiIndexLE (Fin N) 1}
    {g : Lp ℝ p (volume.restrict ((⊤ : Opens 𝔼) : Set 𝔼))} (hg : g = weakDeriv w α) :
    ‖g‖ ≤ ‖w‖ := by
  subst hg
  exact norm_weakDeriv_le w α

/-- **The three-term bound.** Let $p < \infty$ and $u, v \in W^{1,p}(\mathbb{R}^N)$. Let $f$ and $g$
be the functions of $u$ and $v$, and let $f' = \partial_i u$ and $g' = \partial_i v$. Then for
every $h$,
$$\|\tau_{h e_i} f - f - h f'\| \le N |h| \|u - v\|_{W^{1,p}} + \|\tau_{h e_i} g - g - h g'\| +
  |h| \|u - v\|_{W^{1,p}},$$
with the $L^p$ norm on the left and in the middle term.

The first term is the translation estimate for $u - v$, and the last term bounds
$|h| \|f' - g'\|$. -/
theorem norm_translateCurve_sub_sub_smul_le (hp : p ≠ ⊤) (u v : SobolevEuclidean N 1 p ⊤)
    (i : Fin N) {f g f' g' : Lp ℝ p (volume.restrict ((⊤ : Opens 𝔼) : Set 𝔼))}
    (hf : f = fnL ℝ 𝔟 1 p ⊤ volume u) (hg : g = fnL ℝ 𝔟 1 p ⊤ volume v)
    (hf' : f' = weakDeriv u (MultiIndexLE.single i))
    (hg' : g' = weakDeriv v (MultiIndexLE.single i)) (h : ℝ) :
    ‖translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ)) f h - f - h • f'‖
      ≤ N * |h| * ‖u - v‖
        + ‖translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ)) g h - g - h • g'‖
        + |h| * ‖u - v‖ := by
  have key : translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ)) f h - f - h • f'
      = (translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ)) (f - g) h - (f - g))
        + (translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ)) g h - g - h • g')
        + h • (g' - f') := by
    rw [translateCurve_sub_fun (EuclideanSpace.single i (1 : ℝ)) f g h]
    module
  have hA : ‖translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ)) (f - g) h - (f - g)‖
      ≤ N * |h| * ‖u - v‖ :=
    norm_translateCurve_sub_le hp (u - v) i (by rw [hf, hg]; exact (fnL_sub u v).symm) h
  have hC' : ‖h • (g' - f')‖ ≤ |h| * ‖u - v‖ := by
    have h1 : ‖g' - f'‖ ≤ ‖u - v‖ := by
      rw [← _root_.norm_neg, neg_sub]
      exact norm_le_of_eq_weakDeriv (u - v) (by rw [hf', hg']; exact (weakDeriv_sub u v _).symm)
    have h2 : ‖h • (g' - f')‖ = |h| * ‖g' - f'‖ :=
      (norm_smul h _).trans (congrArg (· * _) (Real.norm_eq_abs h))
    rw [h2]
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg h)
  calc _ = ‖_‖ := congrArg norm key
    _ ≤ _ := norm_add₃_le
    _ ≤ _ := add_le_add (add_le_add hA le_rfl) hC'

/-- Let $p < \infty$, $u \in W^{1,p}(\mathbb{R}^N)$ and $\varepsilon > 0$. Let $v$ be the class of a
test function with $\|u - v\|_{W^{1,p}} < \varepsilon / (3 (N + 1))$. Then for all $h$ close
enough to $0$,
$$\|\tau_{h e_i} u - u - h \, \partial_i u\|_{L^p} \le \varepsilon |h|.$$
-/
theorem eventually_norm_translateCurve_sub_sub_smul_le (hp : p ≠ ⊤)
    (u : SobolevEuclidean N 1 p ⊤) {v : SobolevEuclidean N 1 p ⊤}
    (hv : v ∈ testFunctions ℝ 𝔟 1 p ⊤ volume) (i : Fin N) {ε : ℝ} (hε : 0 < ε)
    (huv : ‖u - v‖ < ε / (3 * (N + 1))) :
    ∀ᶠ h in 𝓝 (0 : ℝ),
      ‖translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ)) (fnL ℝ 𝔟 1 p ⊤ volume u) h
        - fnL ℝ 𝔟 1 p ⊤ volume u - h • weakDeriv u (MultiIndexLE.single i)‖ ≤ ε * ‖h‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_translateCurve_sub_sub_smul_le hv i
  have hδ : 0 < min 1 (ε / (3 * (C + 1))) := lt_min one_pos (by positivity)
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with h hh
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, lt_min_iff] at hh
  rw [Real.norm_eq_abs h]
  have e1 : (N + 1) * ‖u - v‖ ≤ ε / 3 := by
    calc (N + 1) * ‖u - v‖ ≤ (N + 1) * (ε / (3 * (N + 1))) := by gcongr
      _ = ε / 3 := by field_simp
  have e2 : C * |h| ≤ ε / 3 := by
    calc C * |h| ≤ C * (ε / (3 * (C + 1))) := by gcongr; exact hh.2.le
      _ ≤ ε / 3 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
        linarith [mul_nonneg hC0 hε.le]
  calc ‖translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ)) (fnL ℝ 𝔟 1 p ⊤ volume u) h
        - fnL ℝ 𝔟 1 p ⊤ volume u - h • weakDeriv u (MultiIndexLE.single i)‖
      ≤ N * |h| * ‖u - v‖
        + ‖translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ)) (fnL ℝ 𝔟 1 p ⊤ volume v) h
          - fnL ℝ 𝔟 1 p ⊤ volume v - h • weakDeriv v (MultiIndexLE.single i)‖
        + |h| * ‖u - v‖ := norm_translateCurve_sub_sub_smul_le hp u v i rfl rfl rfl rfl h
    _ ≤ N * |h| * ‖u - v‖ + C * h ^ 2 + |h| * ‖u - v‖ :=
        add_le_add (add_le_add le_rfl (hC h hh.1.le)) le_rfl
    _ = (N + 1) * ‖u - v‖ * |h| + C * |h| * |h| := by rw [← sq_abs]; ring
    _ ≤ ε / 3 * |h| + ε / 3 * |h| :=
        add_le_add (mul_le_mul_of_nonneg_right e1 (abs_nonneg h))
          (mul_le_mul_of_nonneg_right e2 (abs_nonneg h))
    _ ≤ ε * |h| := by linarith [mul_nonneg hε.le (abs_nonneg h)]

/-- **Derivative at $0$ of the translation curve.** Let $p < \infty$ and
$u \in W^{1,p}(\mathbb{R}^N)$. Then the curve $t \mapsto \tau_{t e_i} u$ in $L^p$ has the
derivative $\partial_i u$ at $t = 0$.

The proof bounds the remainder with `SobolevEuclidean.norm_translateCurve_sub_sub_smul_le`
through a test function close to $u$, and the middle term is $O(h^2)$ by
`SobolevEuclidean.exists_norm_translateCurve_sub_sub_smul_le`. -/
theorem hasDerivAt_translateCurve_fnL_zero (hp : p ≠ ⊤) (u : SobolevEuclidean N 1 p ⊤)
    (i : Fin N) :
    HasDerivAt (translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ)) (fnL ℝ 𝔟 1 p ⊤ volume u))
      (weakDeriv u (MultiIndexLE.single i)) 0 := by
  refine hasDerivAt_iff_isLittleO_nhds_zero.2 (Asymptotics.isLittleO_iff.2 fun ε hε ↦ ?_)
  refine (exists_testFunctions_norm_sub_lt hp u (δ := ε / (3 * (N + 1))) (by positivity)).elim
    fun v hv ↦ ?_
  refine (eventually_norm_translateCurve_sub_sub_smul_le hp u hv.1 i hε hv.2).mono fun h hh ↦ ?_
  rw [zero_add, translateCurve_zero (EuclideanSpace.single i (1 : ℝ)) (fnL ℝ 𝔟 1 p ⊤ volume u)]
  exact hh

/-- **Derivative of the translation curve.** Let $p < \infty$ and $u \in W^{1,p}(\mathbb{R}^N)$.
Then for every $t$ the curve $s \mapsto \tau_{s e_i} u$ in $L^p$ has the derivative
$\tau_{t e_i} \partial_i u$ at $s = t$.

The case $t = 0$ is transported to $t$ by the group law and the isometry $\tau_{t e_i}$. -/
theorem hasDerivAt_translateCurve_fnL (hp : p ≠ ⊤) (u : SobolevEuclidean N 1 p ⊤) (i : Fin N)
    (t : ℝ) :
    HasDerivAt (translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ)) (fnL ℝ 𝔟 1 p ⊤ volume u))
      (translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ))
        (weakDeriv u (MultiIndexLE.single i)) t) t := by
  have h0 := hasDerivAt_translateCurve_fnL_zero hp u i
  have e : translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ)) (fnL ℝ 𝔟 1 p ⊤ volume u)
      = fun s ↦ Lp.translate ℝ p (IsTranslationInvariant.top (t • EuclideanSpace.single i (1 : ℝ)))
        (translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ)) (fnL ℝ 𝔟 1 p ⊤ volume u)
          (s - t)) := by
    funext s
    rw [← translateCurve_add, add_sub_cancel]
  rw [e]
  have h1 : HasDerivAt (translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ))
      (fnL ℝ 𝔟 1 p ⊤ volume u)) (weakDeriv u (MultiIndexLE.single i)) (t - t) := by
    rw [sub_self]; exact h0
  have h2 := h1.comp_sub_const t t
  exact (Lp.translate ℝ p (IsTranslationInvariant.top
    (t • EuclideanSpace.single i (1 : ℝ)))).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t h2

/-- Let $p < \infty$ and $u \in W^{1,p}(\mathbb{R}^N)$. The derivative of the curve
$t \mapsto \tau_{t e_i} u$ in $L^p$ is the curve $t \mapsto \tau_{t e_i} \partial_i u$. -/
theorem deriv_translateCurve_fnL (hp : p ≠ ⊤) (u : SobolevEuclidean N 1 p ⊤) (i : Fin N) :
    deriv (translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ)) (fnL ℝ 𝔟 1 p ⊤ volume u))
      = translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ))
        (weakDeriv u (MultiIndexLE.single i)) :=
  funext fun t ↦ (hasDerivAt_translateCurve_fnL hp u i t).deriv

/-- **The translation curve is $C^k$.** Let $p < \infty$ and $u \in W^{k,p}(\mathbb{R}^N)$. Then the
curve $t \mapsto \tau_{t e_i} u$ is $C^k$ into $L^p$.

The proof is an induction on $k$: the derivative is the translation curve of
$\partial_i u \in W^{k-1,p}(\mathbb{R}^N)$. -/
theorem contDiff_translateCurve_fnL (hp : p ≠ ⊤) {k : ℕ} (u : SobolevEuclidean N k p ⊤)
    (i : Fin N) :
    ContDiff ℝ k (translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ))
      (fnL ℝ 𝔟 k p ⊤ volume u)) := by
  induction k with
  | zero => exact contDiff_zero.2 (continuous_translateCurve _ _ hp)
  | succ k ih =>
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun t ↦ ?_, fun h ↦ by simp at h, ?_⟩
    · exact (hasDerivAt_translateCurve_fnL hp (toLowerOrderL ℝ 𝔟 p ⊤ volume
        (by omega : 1 ≤ k + 1) u) i t).differentiableAt
    · have e : deriv (translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ))
          (fnL ℝ 𝔟 (k + 1) p ⊤ volume u))
          = translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ))
            (fnL ℝ 𝔟 k p ⊤ volume (partialDerivL ℝ 𝔟 p ⊤ volume i u)) := by
        rw [← fnL_toLowerOrderL (by omega : 1 ≤ k + 1) u, deriv_translateCurve_fnL hp,
          weakDeriv_toLowerOrderL_single, fnL_partialDerivL]
      rw [e]
      exact ih _

/-- For indices $i$ and $j$, the multi-indices $e_j + e_i$ and $e_i + e_j$ of order at most two are
equal. Each side adds a unit multi-index to a multi-index of order one. -/
theorem _root_.MultiIndexLE.addSingle_single_comm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) :
    MultiIndexLE.addSingle i (MultiIndexLE.single j)
      = MultiIndexLE.addSingle j (MultiIndexLE.single i) :=
  Subtype.ext (add_comm _ _)

/-- **Strong continuity of the translation group on $W^{k,p}(\mathbb{R}^N)$.** Let $p < \infty$,
$y \in \mathbb{R}^N$ and $w \in W^{k,p}(\mathbb{R}^N)$. Then the curve $t \mapsto \tau_{ty} w$
is continuous into $W^{k,p}(\mathbb{R}^N)$.

Each weak derivative is translated, so the claim follows from the continuity in $L^p$. -/
theorem continuous_translateL_smul (hp : p ≠ ⊤) {k : ℕ} (y : 𝔼) (w : SobolevEuclidean N k p ⊤) :
    Continuous fun t : ℝ ↦ translateL ℝ 𝔟 k p volume (IsTranslationInvariant.top (t • y)) w :=
  continuous_of_forall_weakDeriv fun α ↦ continuous_translateCurve y (weakDeriv w α) hp

/-- **Derivative of the translation curve in $W^{1,p}$.** Let $p < \infty$ and
$u \in W^{2,p}(\mathbb{R}^N)$. Then for every $t$ the curve $s \mapsto \tau_{s e_i} u$ in
$W^{1,p}(\mathbb{R}^N)$ has the derivative $\tau_{t e_i} \partial_i u$ at $s = t$, where
$\partial_i u \in W^{1,p}(\mathbb{R}^N)$.

The element $u$ is read in $W^{1,p}$ through `SobolevMultiIndex.toLowerOrderL`, and
$\partial_i u$ is `SobolevMultiIndex.partialDerivL`. The proof applies
`SobolevEuclidean.hasDerivAt_translateCurve_fnL` to $u$ and to its first derivatives, component
by component. -/
theorem hasDerivAt_translateL (hp : p ≠ ⊤) (u : SobolevEuclidean N 2 p ⊤) (i : Fin N) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ translateL ℝ 𝔟 1 p volume
        (IsTranslationInvariant.top (s • EuclideanSpace.single i (1 : ℝ)))
        (toLowerOrderL ℝ 𝔟 p ⊤ volume (by omega : 1 ≤ 2) u))
      (translateL ℝ 𝔟 1 p volume (IsTranslationInvariant.top (t • EuclideanSpace.single i (1 : ℝ)))
        (partialDerivL ℝ 𝔟 p ⊤ volume i u)) t := by
  refine hasDerivAt_of_forall_weakDeriv fun α ↦ ?_
  rcases MultiIndexLE.eq_zero_or_exists_eq_single α with rfl | ⟨j, rfl⟩
  · change HasDerivAt (translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ))
        (weakDeriv (toLowerOrderL ℝ 𝔟 p ⊤ volume (by omega : 1 ≤ 2) u) 0))
      (translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ))
        (weakDeriv (partialDerivL ℝ 𝔟 p ⊤ volume i u) 0) t) t
    have e1 : weakDeriv (partialDerivL ℝ 𝔟 p ⊤ volume i u) (0 : MultiIndexLE (Fin N) 1)
        = weakDeriv (toLowerOrderL ℝ 𝔟 p ⊤ volume (by omega : 1 ≤ 2) u) (MultiIndexLE.single i) :=
      congrArg (weakDeriv u) (MultiIndexLE.addSingle_zero i)
    rw [e1]
    exact hasDerivAt_translateCurve_fnL hp (toLowerOrderL ℝ 𝔟 p ⊤ volume (by omega : 1 ≤ 2) u) i t
  · change HasDerivAt (translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ))
        (weakDeriv (toLowerOrderL ℝ 𝔟 p ⊤ volume (by omega : 1 ≤ 2) u) (MultiIndexLE.single j)))
      (translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ))
        (weakDeriv (partialDerivL ℝ 𝔟 p ⊤ volume i u) (MultiIndexLE.single j)) t) t
    have e2 : weakDeriv (partialDerivL ℝ 𝔟 p ⊤ volume i u) (MultiIndexLE.single j)
        = weakDeriv (partialDerivL ℝ 𝔟 p ⊤ volume j u) (MultiIndexLE.single i) :=
      congrArg (weakDeriv u) (MultiIndexLE.addSingle_single_comm i j)
    have e3 : weakDeriv (toLowerOrderL ℝ 𝔟 p ⊤ volume (by omega : 1 ≤ 2) u) (MultiIndexLE.single j)
        = fnL ℝ 𝔟 1 p ⊤ volume (partialDerivL ℝ 𝔟 p ⊤ volume j u) :=
      (fnL_partialDerivL (k := 1) j u).symm
    exact (congrArg (fun w ↦ HasDerivAt (translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ)) w)
      (translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ))
        (weakDeriv (partialDerivL ℝ 𝔟 p ⊤ volume i u) (MultiIndexLE.single j)) t) t) e3).mpr
      ((hasDerivAt_translateCurve_fnL hp (partialDerivL ℝ 𝔟 p ⊤ volume j u) i t).congr_deriv
        (congrArg (fun w ↦ translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ)) w t) e2.symm))

/-- **The translation curve is $C^1$ into $W^{1,p}$.** Let $p < \infty$ and
$u \in W^{2,p}(\mathbb{R}^N)$. Then the curve $s \mapsto \tau_{s e_i} u$ is $C^1$ into
$W^{1,p}(\mathbb{R}^N)$. -/
theorem contDiff_translateL (hp : p ≠ ⊤) (u : SobolevEuclidean N 2 p ⊤) (i : Fin N) :
    ContDiff ℝ 1 fun s : ℝ ↦ translateL ℝ 𝔟 1 p volume
      (IsTranslationInvariant.top (s • EuclideanSpace.single i (1 : ℝ)))
      (toLowerOrderL ℝ 𝔟 p ⊤ volume (by omega : 1 ≤ 2) u) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t ↦ (hasDerivAt_translateL hp u i t).differentiableAt, ?_⟩
  have e : deriv (fun s : ℝ ↦ translateL ℝ 𝔟 1 p volume
      (IsTranslationInvariant.top (s • EuclideanSpace.single i (1 : ℝ)))
      (toLowerOrderL ℝ 𝔟 p ⊤ volume (by omega : 1 ≤ 2) u))
      = fun t ↦ translateL ℝ 𝔟 1 p volume
        (IsTranslationInvariant.top (t • EuclideanSpace.single i (1 : ℝ)))
        (partialDerivL ℝ 𝔟 p ⊤ volume i u) :=
    funext fun t ↦ (hasDerivAt_translateL hp u i t).deriv
  rw [e]
  exact continuous_translateL_smul hp _ _

/-- Let $p < \infty$ and $u \in W^{2,p}(\mathbb{R}^N)$. Then the curve
$s \mapsto \tau_{s e_i} u + \tau_{-s e_i} u$ is $C^1$ into $W^{1,p}(\mathbb{R}^N)$. -/
theorem contDiff_translateL_add_neg (hp : p ≠ ⊤) (u : SobolevEuclidean N 2 p ⊤) (i : Fin N) :
    ContDiff ℝ 1 fun s : ℝ ↦ translateL ℝ 𝔟 1 p volume
        (IsTranslationInvariant.top (s • EuclideanSpace.single i (1 : ℝ)))
        (toLowerOrderL ℝ 𝔟 p ⊤ volume (by omega : 1 ≤ 2) u)
      + translateL ℝ 𝔟 1 p volume
        (IsTranslationInvariant.top ((-s) • EuclideanSpace.single i (1 : ℝ)))
        (toLowerOrderL ℝ 𝔟 p ⊤ volume (by omega : 1 ≤ 2) u) :=
  (contDiff_translateL hp u i).add ((contDiff_translateL hp u i).comp contDiff_neg)

end SobolevEuclidean

end Deriv

/-! ### The primitive curve $t \mapsto \int_{-t}^{t} \tau_{sy} f \, ds$ -/

/-- **Cauchy–Schwarz on a set of finite measure.** Let $g \in L^2(\nu)$ be real-valued and let $A$
have finite measure. Then
$$\int_A |g| \, d\nu \le \|g\|_{L^2(\nu)} \, \nu(A)^{1/2}.$$
-/
theorem MeasureTheory.integral_norm_restrict_le_of_memLp_two {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {g : X → ℝ} (hg : MemLp g 2 ν) {A : Set X} (hA : ν A ≠ ⊤) :
    ∫ x in A, ‖g x‖ ∂ν ≤ (eLpNorm g 2 ν).toReal * (ν A).toReal ^ (1 / 2 : ℝ) := by
  have hA' : (ν.restrict A) univ ≠ ⊤ := by rwa [Measure.restrict_apply_univ]
  have hgA : AEStronglyMeasurable g (ν.restrict A) := hg.aestronglyMeasurable.restrict
  rw [integral_norm_eq_lintegral_enorm hgA, ← eLpNorm_one_eq_lintegral_enorm hgA]
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := ν.restrict A) (p := 1) (q := 2)
    one_le_two hgA
  have h' : eLpNorm g 2 (ν.restrict A) ≤ eLpNorm g 2 ν :=
    eLpNorm_mono_measure _ Measure.restrict_le_self
  have e : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) := by norm_num
  rw [e] at h
  have h'' : eLpNorm g 2 (ν.restrict A) * (ν.restrict A) univ ^ (1 / 2 : ℝ)
      ≤ eLpNorm g 2 ν * (ν.restrict A) univ ^ (1 / 2 : ℝ) := by gcongr
  refine (ENNReal.toReal_mono ?_ (h.trans h'')).trans ?_
  · exact ENNReal.mul_ne_top hg.eLpNorm_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hA')
  · rw [ENNReal.toReal_mul, Measure.restrict_apply_univ, ENNReal.toReal_rpow]

section Primitive

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

namespace MeasureTheory.Lp

/-- Let $E$ be finite-dimensional with an additive Haar measure $\mu$, and let $y \in E$. The map
$(s, x) \mapsto x + s y$ is quasi-measure-preserving from the product of Lebesgue measure and
$\mu$ to $\mu$.

The fibres of the map are translations, which preserve $\mu$. -/
theorem quasiMeasurePreserving_add_smul (y : E) :
    QuasiMeasurePreserving (fun z : ℝ × E ↦ z.2 + z.1 • y)
      (volume.prod (μ.restrict ((⊤ : Opens E) : Set E))) (μ.restrict ((⊤ : Opens E) : Set E)) := by
  have hm : Measurable (fun z : ℝ × E ↦ z.2 + z.1 • y) := by fun_prop
  refine ⟨hm, Measure.AbsolutelyContinuous.mk fun A hA hA0 ↦ ?_⟩
  rw [Measure.map_apply hm hA, Measure.prod_apply (hm hA)]
  have h : ∀ s : ℝ, μ.restrict ((⊤ : Opens E) : Set E)
      (Prod.mk s ⁻¹' ((fun z : ℝ × E ↦ z.2 + z.1 • y) ⁻¹' A)) = 0 := fun s ↦ by
    have := ((IsTranslationInvariant.top (s • y)).measurePreserving (μ := μ)).measure_preimage
      hA.nullMeasurableSet
    rw [hA0] at this
    exact this
  simp only [h, lintegral_zero]

variable (y : E) (f : Lp ℝ 2 (μ.restrict ((⊤ : Opens E) : Set E)))

/-- For $f \in L^2(E)$ and $y \in E$, the function $(s, x) \mapsto f(x + s y) + f(x - s y)$ is
almost everywhere strongly measurable on $\mathbb{R} \times E$. -/
theorem aestronglyMeasurable_add_smul_add_sub_smul :
    AEStronglyMeasurable (fun z : ℝ × E ↦ f (z.2 + z.1 • y) + f (z.2 - z.1 • y))
      (volume.prod (μ.restrict ((⊤ : Opens E) : Set E))) := by
  have h1 := (Lp.aestronglyMeasurable f).comp_quasiMeasurePreserving
    (quasiMeasurePreserving_add_smul (μ := μ) y)
  have h2 := (Lp.aestronglyMeasurable f).comp_quasiMeasurePreserving
    (quasiMeasurePreserving_add_smul (μ := μ) (-y))
  refine h1.add (h2.congr (Eventually.of_forall fun z ↦ ?_))
  simp only [Function.comp_apply, smul_neg, sub_eq_add_neg]

/-- Let $f \in L^2(E)$ and $y \in E$. For sets $I \subseteq \mathbb{R}$ and $A \subseteq E$ of
finite measure, the function $(s, x) \mapsto f(x + s y) + f(x - s y)$ is integrable on
$I \times A$. -/
theorem integrable_add_smul_add_sub_smul {I : Set ℝ} (hI : volume I ≠ ⊤)
    {A : Set E} (hA : μ.restrict ((⊤ : Opens E) : Set E) A ≠ ⊤) :
    Integrable (fun z : ℝ × E ↦ f (z.2 + z.1 • y) + f (z.2 - z.1 • y))
      ((volume.restrict I).prod ((μ.restrict ((⊤ : Opens E) : Set E)).restrict A)) := by
  have hmeas : AEStronglyMeasurable (fun z : ℝ × E ↦ f (z.2 + z.1 • y) + f (z.2 - z.1 • y))
      ((volume.restrict I).prod ((μ.restrict ((⊤ : Opens E) : Set E)).restrict A)) := by
    rw [Measure.prod_restrict]
    exact (aestronglyMeasurable_add_smul_add_sub_smul y f).restrict
  have : IsFiniteMeasure ((μ.restrict ((⊤ : Opens E) : Set E)).restrict A) :=
    ⟨by rwa [Measure.restrict_apply_univ, lt_top_iff_ne_top]⟩
  have : IsFiniteMeasure (volume.restrict I) :=
    ⟨by rwa [Measure.restrict_apply_univ, lt_top_iff_ne_top]⟩
  have m1 : ∀ s : ℝ, MemLp (fun x ↦ f (x + s • y)) 2 (μ.restrict ((⊤ : Opens E) : Set E)) :=
    fun s ↦ (Lp.memLp f).comp_add_right (IsTranslationInvariant.top _)
  have m2 : ∀ s : ℝ, MemLp (fun x ↦ f (x - s • y)) 2 (μ.restrict ((⊤ : Opens E) : Set E)) :=
    fun s ↦ by
      have := (Lp.memLp f).comp_add_right (IsTranslationInvariant.top (-(s • y)))
      simpa only [sub_eq_add_neg] using this
  have e1 : ∀ s : ℝ, eLpNorm (fun x ↦ f (x + s • y)) 2 (μ.restrict ((⊤ : Opens E) : Set E))
      = eLpNorm f 2 (μ.restrict ((⊤ : Opens E) : Set E)) := fun s ↦
    eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable f)
      (IsTranslationInvariant.top (s • y)).measurePreserving
  have e2 : ∀ s : ℝ, eLpNorm (fun x ↦ f (x - s • y)) 2 (μ.restrict ((⊤ : Opens E) : Set E))
      = eLpNorm f 2 (μ.restrict ((⊤ : Opens E) : Set E)) := fun s ↦ by
    have := eLpNorm_comp_measurePreserving (p := 2) (Lp.aestronglyMeasurable f)
      (IsTranslationInvariant.top (-(s • y))).measurePreserving
    simpa only [Function.comp_def, sub_eq_add_neg] using this
  refine (integrable_prod_iff hmeas).2 ⟨Eventually.of_forall fun s ↦ ?_, ?_⟩
  · exact (((m1 s).restrict A).integrable one_le_two).add
      (((m2 s).restrict A).integrable one_le_two)
  · set C : ℝ := (eLpNorm f 2 (μ.restrict ((⊤ : Opens E) : Set E))).toReal
      * ((μ.restrict ((⊤ : Opens E) : Set E)) A).toReal ^ (1 / 2 : ℝ) with hC
    refine Integrable.mono' (integrable_const (2 * C)) hmeas.norm.integral_prod_right'
      (Eventually.of_forall fun s ↦ ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
    calc ∫ x, ‖f (x + s • y) + f (x - s • y)‖ ∂((μ.restrict ((⊤ : Opens E) : Set E)).restrict A)
        ≤ ∫ x, (‖f (x + s • y)‖ + ‖f (x - s • y)‖)
            ∂((μ.restrict ((⊤ : Opens E) : Set E)).restrict A) :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ norm_nonneg _)
            ((((m1 s).restrict A).integrable one_le_two).norm.add
              (((m2 s).restrict A).integrable one_le_two).norm)
            (Eventually.of_forall fun x ↦ norm_add_le _ _)
      _ = (∫ x, ‖f (x + s • y)‖ ∂((μ.restrict ((⊤ : Opens E) : Set E)).restrict A))
          + ∫ x, ‖f (x - s • y)‖ ∂((μ.restrict ((⊤ : Opens E) : Set E)).restrict A) :=
          integral_add (((m1 s).restrict A).integrable one_le_two).norm
            (((m2 s).restrict A).integrable one_le_two).norm
      _ ≤ C + C := by
          refine add_le_add ?_ ?_
          · have := MeasureTheory.integral_norm_restrict_le_of_memLp_two (m1 s) hA
            rwa [e1] at this
          · have := MeasureTheory.integral_norm_restrict_le_of_memLp_two (m2 s) hA
            rwa [e2] at this
      _ = 2 * C := by ring

end MeasureTheory.Lp

end Primitive

section PrimitiveCurve

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace MeasureTheory.Lp

variable (F p) in
/-- **The primitive curve** of $f \in L^p(E)$ along the direction $y$: the curve
$$t \mapsto \int_0^t (\tau_{sy} f + \tau_{-sy} f) \, ds = \int_{-t}^{t} \tau_{sy} f \, ds$$
in $L^p(E)$, where the integral is a Bochner integral in $L^p$.

At $p = 2$ it is the class of $x \mapsto \int_{-t}^{t} f(x + s y) \, ds$, by
`MeasureTheory.Lp.coeFn_primitiveCurve`. -/
def primitiveCurve (y : E) (f : Lp F p (μ.restrict ((⊤ : Opens E) : Set E))) (t : ℝ) :
    Lp F p (μ.restrict ((⊤ : Opens E) : Set E)) :=
  ∫ s in (0 : ℝ)..t, (translateCurve F p y f s + translateCurve F p y f (-s))

variable (y : E) (f : Lp F p (μ.restrict ((⊤ : Opens E) : Set E)))

/-- The primitive curve vanishes at $t = 0$. -/
theorem primitiveCurve_zero : primitiveCurve F p y f 0 = 0 :=
  intervalIntegral.integral_same

/-- Let $E$ be finite-dimensional and $p < \infty$. The integrand
$s \mapsto \tau_{sy} f + \tau_{-sy} f$ of the primitive curve is continuous into $L^p$. -/
theorem continuous_translateCurve_add_neg [FiniteDimensional ℝ E] (hp : p ≠ ⊤) :
    Continuous fun s ↦ translateCurve F p y f s + translateCurve F p y f (-s) :=
  (continuous_translateCurve y f hp).add ((continuous_translateCurve y f hp).comp continuous_neg)

/-- Let $E$ be finite-dimensional and $p < \infty$. The curve $s \mapsto \tau_{sy} f - \tau_{-sy} f$
is continuous into $L^p$. -/
theorem continuous_translateCurve_sub_neg [FiniteDimensional ℝ E] (hp : p ≠ ⊤) :
    Continuous fun s ↦ translateCurve F p y f s - translateCurve F p y f (-s) :=
  (continuous_translateCurve y f hp).sub ((continuous_translateCurve y f hp).comp continuous_neg)

/-- **Derivative of the primitive curve.** Let $E$ be finite-dimensional, $F$ complete and
$p < \infty$. Then for every $t$ the primitive curve of $f$ along $y$ has the derivative
$\tau_{ty} f + \tau_{-ty} f$ at $t$.

This is the fundamental theorem of calculus for a continuous $L^p$-valued integrand. -/
theorem hasDerivAt_primitiveCurve [FiniteDimensional ℝ E] [CompleteSpace F] (hp : p ≠ ⊤) (t : ℝ) :
    HasDerivAt (primitiveCurve F p y f)
      (translateCurve F p y f t + translateCurve F p y f (-t)) t :=
  intervalIntegral.integral_hasDerivAt_right
    ((continuous_translateCurve_add_neg y f hp).intervalIntegrable _ _)
    ((continuous_translateCurve_add_neg y f hp).stronglyMeasurableAtFilter _ _)
    (continuous_translateCurve_add_neg y f hp).continuousAt

/-- Let $E$ be finite-dimensional, $F$ complete and $p < \infty$. The primitive curve is $C^1$ into
$L^p$. -/
theorem contDiff_primitiveCurve [FiniteDimensional ℝ E] [CompleteSpace F] (hp : p ≠ ⊤) :
    ContDiff ℝ 1 (primitiveCurve F p y f) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t ↦ (hasDerivAt_primitiveCurve y f hp t).differentiableAt, ?_⟩
  have e : deriv (primitiveCurve F p y f)
      = fun t ↦ translateCurve F p y f t + translateCurve F p y f (-t) :=
    funext fun t ↦ (hasDerivAt_primitiveCurve y f hp t).deriv
  rw [e]
  exact continuous_translateCurve_add_neg y f hp

/-- The primitive curve is odd: its value at $-t$ is the negative of its value at $t$. -/
theorem primitiveCurve_neg (t : ℝ) : primitiveCurve F p y f (-t) = -primitiveCurve F p y f t := by
  set G : ℝ → Lp F p (μ.restrict ((⊤ : Opens E) : Set E)) :=
    fun s ↦ translateCurve F p y f s + translateCurve F p y f (-s) with hG
  have hsymm : ∀ s, G (-s) = G s := fun s ↦ by
    simp only [hG, neg_neg, add_comm]
  calc primitiveCurve F p y f (-t) = ∫ s in (0 : ℝ)..(-t), G (-s) :=
        intervalIntegral.integral_congr fun s _ ↦ (hsymm s).symm
    _ = ∫ s in t..0, G s := by rw [intervalIntegral.integral_comp_neg, neg_neg, neg_zero]
    _ = -primitiveCurve F p y f t := intervalIntegral.integral_symm 0 t

end MeasureTheory.Lp

end PrimitiveCurve

section Identification

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

namespace MeasureTheory.Lp

variable (y : E) (f : Lp ℝ 2 (μ.restrict ((⊤ : Opens E) : Set E)))

/-- For $c \in \mathbb{R}$ and $f, g, h \in L^2(\mu)$, the class $c (f + g) + c h$ agrees almost
everywhere with $x \mapsto c (f(x) + g(x)) + c \, h(x)$. -/
theorem coeFn_smul_add_add_smul {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (c : ℝ) (f g h : Lp ℝ 2 μ) :
    ⇑(c • (f + g) + c • h) =ᵐ[μ] fun x ↦ c * (f x + g x) + c * h x := by
  filter_upwards [Lp.coeFn_add (c • (f + g)) (c • h), Lp.coeFn_smul c (f + g), Lp.coeFn_smul c h,
    Lp.coeFn_add f g] with x h1 h2 h3 h4
  rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, Pi.smul_apply, h4, Pi.add_apply, smul_eq_mul,
    smul_eq_mul]

/-- Let $E$ be finite-dimensional with an additive Haar measure, let $f \in L^2(E)$ and $y \in E$,
and let $I \subseteq \mathbb{R}$ have finite measure. Then the Bochner integral
$\int_I (\tau_{sy} f + \tau_{-sy} f) \, ds$ in $L^2$ agrees almost everywhere with
$$x \mapsto \int_I (f(x + s y) + f(x - s y)) \, ds.$$

Both sides have the same integral over every set $A$ of finite measure. On the left, the pairing
with the indicator of $A$ is a bounded functional on $L^2$ and passes through the Bochner
integral. On the right, Fubini's theorem applies on $I \times A$. -/
theorem coeFn_setIntegral_translateCurve_add_neg {I : Set ℝ} (hIfin : volume I ≠ ⊤) :
    ⇑(∫ s in I, (translateCurve ℝ 2 y f s + translateCurve ℝ 2 y f (-s)))
      =ᵐ[μ.restrict ((⊤ : Opens E) : Set E)]
        fun x ↦ ∫ s in I, (f (x + s • y) + f (x - s • y)) := by
  set G : ℝ → Lp ℝ 2 (μ.restrict ((⊤ : Opens E) : Set E)) :=
    fun s ↦ translateCurve ℝ 2 y f s + translateCurve ℝ 2 y f (-s) with hG
  have hGc : Continuous G := continuous_translateCurve_add_neg y f (by simp)
  have hIfin' : IsFiniteMeasure (volume.restrict I) :=
    ⟨by rwa [Measure.restrict_apply_univ, lt_top_iff_ne_top]⟩
  have hGi : IntegrableOn G I := by
    refine Integrable.mono' (integrable_const (2 * ‖f‖)) hGc.aestronglyMeasurable
      (Eventually.of_forall fun s ↦ ?_)
    calc ‖G s‖ ≤ ‖translateCurve ℝ 2 y f s‖ + ‖translateCurve ℝ 2 y f (-s)‖ := norm_add_le _ _
      _ = 2 * ‖f‖ := by rw [norm_translateCurve, norm_translateCurve]; ring
  -- the coefficient functions of `G s`
  have hGae : ∀ s, ⇑(G s) =ᵐ[μ.restrict ((⊤ : Opens E) : Set E)]
      fun x ↦ f (x + s • y) + f (x - s • y) := fun s ↦ by
    filter_upwards [Lp.coeFn_add (translateCurve ℝ 2 y f s) (translateCurve ℝ 2 y f (-s)),
      coeFn_translateCurve y f s, coeFn_translateCurve y f (-s)] with x h1 h2 h3
    rw [hG]
    dsimp only
    rw [h1, Pi.add_apply, h2, h3, neg_smul, ← sub_eq_add_neg]
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (fun A hA hAfin ↦ ?_)
    (fun A hA hAfin ↦ ?_) fun A hA hAfin ↦ ?_
  · have : IsFiniteMeasure ((μ.restrict ((⊤ : Opens E) : Set E)).restrict A) :=
      ⟨by rwa [Measure.restrict_apply_univ]⟩
    exact ((Lp.memLp _).restrict A).integrable one_le_two
  · exact (integrable_add_smul_add_sub_smul y f hIfin hAfin.ne).integral_prod_right
  · have h1 : ∫ x in A, (∫ s in I, G s) x ∂(μ.restrict ((⊤ : Opens E) : Set E))
        = ∫ s in I, ∫ x in A, (f (x + s • y) + f (x - s • y))
          ∂(μ.restrict ((⊤ : Opens E) : Set E)) := by
      have e0 : ∫ x in A, (∫ s in I, G s) x ∂(μ.restrict ((⊤ : Opens E) : Set E))
          = innerSL ℝ (indicatorConstLp 2 hA hAfin.ne (1 : ℝ)) (∫ s in I, G s) :=
        (L2.inner_indicatorConstLp_one hA hAfin.ne _).symm
      rw [e0, ← (innerSL ℝ (indicatorConstLp 2 hA hAfin.ne (1 : ℝ))).integral_comp_comm hGi]
      refine integral_congr_ae (Eventually.of_forall fun s ↦ ?_)
      change ⟪indicatorConstLp 2 hA hAfin.ne (1 : ℝ), G s⟫_ℝ = _
      rw [L2.inner_indicatorConstLp_one hA hAfin.ne]
      exact setIntegral_congr_ae hA ((hGae s).mono fun x hx _ ↦ hx)
    have h2 : ∫ x in A, (∫ s in I, (f (x + s • y) + f (x - s • y)))
          ∂(μ.restrict ((⊤ : Opens E) : Set E))
        = ∫ s in I, ∫ x in A, (f (x + s • y) + f (x - s • y))
          ∂(μ.restrict ((⊤ : Opens E) : Set E)) :=
      (integral_integral_swap (integrable_add_smul_add_sub_smul y f hIfin hAfin.ne)).symm
    rw [h1, h2]

/-- **The primitive curve as a pointwise integral.** Let $E$ be finite-dimensional with an additive
Haar measure, let $f \in L^2(E)$ and $y \in E$. Then for every $t$ the primitive curve of $f$
along $y$ at $t$ agrees almost everywhere with
$$x \mapsto \int_0^t (f(x + s y) + f(x - s y)) \, ds = \int_{-t}^{t} f(x + s y) \, ds.$$
-/
theorem coeFn_primitiveCurve (t : ℝ) :
    primitiveCurve ℝ 2 y f t =ᵐ[μ.restrict ((⊤ : Opens E) : Set E)]
      fun x ↦ ∫ s in (0 : ℝ)..t, (f (x + s • y) + f (x - s • y)) := by
  rcases le_or_gt 0 t with ht | ht
  · have e : primitiveCurve ℝ 2 y f t
        = ∫ s in Ioc 0 t, (translateCurve ℝ 2 y f s + translateCurve ℝ 2 y f (-s)) :=
      intervalIntegral.integral_of_le ht
    rw [e]
    refine (coeFn_setIntegral_translateCurve_add_neg y f
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)).trans
      (Eventually.of_forall fun x ↦ ?_)
    exact (intervalIntegral.integral_of_le ht).symm
  · have e : primitiveCurve ℝ 2 y f t
        = -∫ s in Ioc t 0, (translateCurve ℝ 2 y f s + translateCurve ℝ 2 y f (-s)) := by
      rw [primitiveCurve, intervalIntegral.integral_symm, intervalIntegral.integral_of_le ht.le]
    rw [e]
    refine (Lp.coeFn_neg _).trans (((coeFn_setIntegral_translateCurve_add_neg y f
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)).neg).trans
      (Eventually.of_forall fun x ↦ ?_))
    simp only [Pi.neg_apply]
    rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le ht.le]

end MeasureTheory.Lp

end Identification

section PrimitiveSobolev

variable {N : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

local notation "𝔼" => EuclideanSpace ℝ (Fin N)
local notation "𝔟" => OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin N) ℝ)

open SobolevMultiIndex MeasureTheory.Lp

namespace SobolevEuclidean

/-- Let $p < \infty$, $y \in \mathbb{R}^N$ and $w \in W^{k,p}(\mathbb{R}^N)$. The curve
$s \mapsto \tau_{sy} w + \tau_{-sy} w$ is continuous into $W^{k,p}(\mathbb{R}^N)$. -/
theorem continuous_translateL_add_neg (hp : p ≠ ⊤) {k : ℕ} (y : 𝔼)
    (w : SobolevEuclidean N k p ⊤) :
    Continuous fun s : ℝ ↦ translateL ℝ 𝔟 k p volume (IsTranslationInvariant.top (s • y)) w
      + translateL ℝ 𝔟 k p volume (IsTranslationInvariant.top ((-s) • y)) w :=
  (continuous_translateL_smul hp y w).add ((continuous_translateL_smul hp y w).comp continuous_neg)

/-- **The primitive curve in $W^{k,p}(\mathbb{R}^N)$.** For $w \in W^{k,p}(\mathbb{R}^N)$ and
$y \in \mathbb{R}^N$, this is the curve
$$t \mapsto \int_0^t (\tau_{sy} w + \tau_{-sy} w) \, ds,$$
where the integral is a Bochner integral in $W^{k,p}(\mathbb{R}^N)$.

Its weak derivatives are the primitive curves of the weak derivatives of $w$, by
`SobolevEuclidean.weakDeriv_primitiveCurveL`. -/
def primitiveCurveL (k : ℕ) (y : 𝔼) (w : SobolevEuclidean N k p ⊤) (t : ℝ) :
    SobolevEuclidean N k p ⊤ :=
  ∫ s in (0 : ℝ)..t, (translateL ℝ 𝔟 k p volume (IsTranslationInvariant.top (s • y)) w
    + translateL ℝ 𝔟 k p volume (IsTranslationInvariant.top ((-s) • y)) w)

variable (hp : p ≠ ⊤) {k : ℕ} (y : EuclideanSpace ℝ (Fin N)) (w : SobolevEuclidean N k p ⊤)
include hp

/-- Let $p < \infty$. For every multi-index $\alpha$ with $|\alpha| \le k$, the weak derivative
$\partial^\alpha$ of the primitive curve of $w$ in $W^{k,p}(\mathbb{R}^N)$ is the primitive
curve of $\partial^\alpha w$ in $L^p$.

The bounded linear map $\partial^\alpha$ passes through the Bochner integral. -/
theorem weakDeriv_primitiveCurveL (t : ℝ) (α : MultiIndexLE (Fin N) k) :
    weakDeriv (primitiveCurveL k y w t) α = primitiveCurve ℝ p y (weakDeriv w α) t := by
  unfold primitiveCurveL primitiveCurve
  rw [← weakDerivL_apply, ← (weakDerivL ℝ 𝔟 k p ⊤ volume α).intervalIntegral_comp_comm
    ((continuous_translateL_add_neg hp y w).intervalIntegrable _ _)]
  refine intervalIntegral.integral_congr fun s _ ↦ ?_
  simp only [map_add, weakDerivL_apply, weakDeriv_translateL]
  rfl

/-- Let $p < \infty$. The function of the primitive curve of $w$ in $W^{k,p}(\mathbb{R}^N)$ is the
primitive curve in $L^p$ of the function of $w$. -/
theorem fnL_primitiveCurveL (t : ℝ) :
    fnL ℝ 𝔟 k p ⊤ volume (primitiveCurveL k y w t)
      = primitiveCurve ℝ p y (fnL ℝ 𝔟 k p ⊤ volume w) t :=
  weakDeriv_primitiveCurveL hp y w t 0

/-- **Derivative of the primitive curve in $W^{k,p}$.** Let $p < \infty$. For every $t$, the
primitive curve of $w$ along $y$ in $W^{k,p}(\mathbb{R}^N)$ has the derivative
$\tau_{ty} w + \tau_{-ty} w$ at $t$. -/
theorem hasDerivAt_primitiveCurveL (t : ℝ) :
    HasDerivAt (primitiveCurveL k y w)
      (translateL ℝ 𝔟 k p volume (IsTranslationInvariant.top (t • y)) w
        + translateL ℝ 𝔟 k p volume (IsTranslationInvariant.top ((-t) • y)) w) t := by
  have : SecondCountableTopologyEither ℝ (SobolevEuclidean N k p ⊤) :=
    secondCountableTopologyEither_of_left ℝ _
  exact intervalIntegral.integral_hasDerivAt_right
    ((continuous_translateL_add_neg hp y w).intervalIntegrable _ _)
    ((continuous_translateL_add_neg hp y w).stronglyMeasurableAtFilter _ _)
    (continuous_translateL_add_neg hp y w).continuousAt

/-- Let $p < \infty$. The primitive curve of $w$ along $y$ is $C^1$ into $W^{k,p}(\mathbb{R}^N)$. -/
theorem contDiff_primitiveCurveL : ContDiff ℝ 1 (primitiveCurveL k y w) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t ↦ (hasDerivAt_primitiveCurveL hp y w t).differentiableAt, ?_⟩
  have e : deriv (primitiveCurveL k y w)
      = fun t ↦ translateL ℝ 𝔟 k p volume (IsTranslationInvariant.top (t • y)) w
        + translateL ℝ 𝔟 k p volume (IsTranslationInvariant.top ((-t) • y)) w :=
    funext fun t ↦ (hasDerivAt_primitiveCurveL hp y w t).deriv
  rw [e]
  exact continuous_translateL_add_neg hp y w

omit hp in
/-- The primitive curve in $W^{k,p}(\mathbb{R}^N)$ vanishes at $t = 0$. -/
theorem primitiveCurveL_zero : primitiveCurveL k y w 0 = 0 :=
  intervalIntegral.integral_same

/-- Let $p < \infty$ and $u \in W^{1,p}(\mathbb{R}^N)$. For every $s$, the curve
$r \mapsto \tau_{r e_i} u - \tau_{-r e_i} u$ in $L^p$ has at $s$ the derivative $\tau_{s e_i}
\partial_i u + \tau_{-s e_i} \partial_i u$. -/
theorem hasDerivAt_translateCurve_sub_neg (u : SobolevEuclidean N 1 p ⊤) (i : Fin N) (s : ℝ) :
    HasDerivAt (fun s ↦ translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ))
        (fnL ℝ 𝔟 1 p ⊤ volume u) s
      - translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ)) (fnL ℝ 𝔟 1 p ⊤ volume u) (-s))
      (translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ)) (weakDeriv u (MultiIndexLE.single i)) s
        + translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ))
          (weakDeriv u (MultiIndexLE.single i)) (-s)) s := by
  have h1 := hasDerivAt_translateCurve_fnL hp u i s
  have h2 := (hasDerivAt_translateCurve_fnL hp u i (-s)).scomp s (hasDerivAt_neg s)
  have h3 := h1.sub h2
  rw [neg_one_smul, sub_neg_eq_add] at h3
  exact h3

/-- Let $p < \infty$ and $u \in W^{1,p}(\mathbb{R}^N)$. For every $s$, the curve
$r \mapsto \tau_{r e_i} u + \tau_{-r e_i} u$ in $L^p$ has at $s$ the derivative $\tau_{s e_i}
\partial_i u - \tau_{-s e_i} \partial_i u$. -/
theorem hasDerivAt_translateCurve_add_neg (u : SobolevEuclidean N 1 p ⊤) (i : Fin N)
    (s : ℝ) :
    HasDerivAt (fun s ↦ translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ))
        (fnL ℝ 𝔟 1 p ⊤ volume u) s
      + translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ)) (fnL ℝ 𝔟 1 p ⊤ volume u) (-s))
      (translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ)) (weakDeriv u (MultiIndexLE.single i)) s
        - translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ))
          (weakDeriv u (MultiIndexLE.single i)) (-s)) s := by
  have h1 := hasDerivAt_translateCurve_fnL hp u i s
  have h2 := (hasDerivAt_translateCurve_fnL hp u i (-s)).scomp s (hasDerivAt_neg s)
  have h3 := h1.add h2
  rw [neg_one_smul, ← sub_eq_add_neg] at h3
  exact h3

/-- **The primitive curve of a partial derivative.** Let $p < \infty$ and
$u \in W^{1,p}(\mathbb{R}^N)$. Then for every $t$, the primitive curve of $\partial_i u$ along
$e_i$ satisfies
$$\int_{-t}^{t} \tau_{s e_i} \partial_i u \, ds = \tau_{t e_i} u - \tau_{-t e_i} u.$$

This is the fundamental theorem of calculus in $L^p$ for the curve
$s \mapsto \tau_{s e_i} u - \tau_{-s e_i} u$. -/
theorem primitiveCurve_weakDeriv_single (u : SobolevEuclidean N 1 p ⊤) (i : Fin N) (t : ℝ) :
    primitiveCurve ℝ p (EuclideanSpace.single i (1 : ℝ)) (weakDeriv u (MultiIndexLE.single i)) t
      = translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ)) (fnL ℝ 𝔟 1 p ⊤ volume u) t
        - translateCurve ℝ p (EuclideanSpace.single i (1 : ℝ)) (fnL ℝ 𝔟 1 p ⊤ volume u) (-t) := by
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ ↦ hasDerivAt_translateCurve_sub_neg hp u i s)
    ((continuous_translateCurve_add_neg (EuclideanSpace.single i (1 : ℝ))
      (weakDeriv u (MultiIndexLE.single i)) hp).intervalIntegrable 0 t)
  rw [neg_zero, sub_self, sub_zero] at this
  exact this

end SobolevEuclidean

end PrimitiveSobolev

end
