/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Sobolev.Translate
import Numlib.Analysis.Sobolev.Interval.Zero
import Numlib.Variational.EllipticInterval
import Numlib.Variational.Inequality.Basic

/-!
# Boundary value problems on an interval: regularity and other boundary conditions

This module treats the boundary value problems of [brezis2011functional], §8.4, other than the
homogeneous Dirichlet problem of `Numlib.Variational.EllipticInterval`. On a bounded interval
$(a, b)$ the bilinear form is $a(u, v) = \int_a^b (\alpha u' v' + \beta u' v + \gamma u v)$ on
$H^1(a, b)$, and the model operator $-u'' + u$ has the form $a(u, v) = \int_a^b (u' v' + u v)$,
which is the inner product of $H^1(a, b)$. For $v \in H^1(a, b)$, $v(a)$ and $v(b)$ are the values
of its continuous representative. For $\Phi \in H^2(a, b)$, $\Phi'(a)$ and $\Phi'(b)$ are the values
of the continuous representative of $\Phi' \in H^1(a, b)$.

The module proves the regularity Steps C and D of the source in the generality that the examples
need: a weak solution tested against $H^1_0(a, b)$ alone is in $H^2(a, b)$; it is $C^2$ when the
data are continuous; a $C^2$ weak solution is a classical solution; and $f \in H^k$ implies
$u \in H^{k+2}$ (Remark 23). It recovers the natural boundary conditions from a weak formulation on
a space larger than $H^1_0(a, b)$, which is the common step of Examples 3–7. It then solves the
inhomogeneous Dirichlet problem of Example 1 (Proposition 8.16), the Neumann problems (Propositions
8.17 and 8.18), the mixed, Robin and periodic problems of Examples 5–7, and the problem
$-u'' + u = f$ on $\mathbb{R}$ of Example 8 in $H^1(\mathbb{R})$. Each strong problem on $(a, b)$
has exactly one solution in $H^2(a, b)$, the solution is $C^2$ when $f$ is continuous, and the
variational characterizations hold.

## Main definitions

* `EllipticInterval.affineLift`: the affine function with the values $\alpha$ at $a$ and $\beta$ at
  $b$, as an element of $H^m(a, b)$.
* `EllipticInterval.dirichletSet`: the closed convex set $\{v \in H^1(a, b) : v(a) = \alpha, v(b) =
  \beta\}$ of Example 1.
* `EllipticInterval.mixedSpace`, `EllipticInterval.robinSpace`, `EllipticInterval.periodicSpace`:
  the closed subspaces $\{v(a) = 0\}$, $\{v(b) = 0\}$ and $\{v(a) = v(b)\}$ of $H^1(a, b)$ for
  Examples 5–7.
* `EllipticInterval.neumannLoad`: the load $v \mapsto \int_a^b f v - \alpha v(a) + \beta v(b)$ of
  the inhomogeneous Neumann problem.
* `EllipticInterval.robinForm`: the form $\int_a^b (u' v' + u v) + k u(a) v(a)$ of the Robin
  problem.
* `EllipticInterval.Line.solution`: the weak solution in $H^1(\mathbb{R})$ of $-u'' + u = f$ on
  $\mathbb{R}$.
* `EllipticInterval.Line.translateLp`, `EllipticInterval.Line.translate`: the translations
  $f \mapsto f(\cdot + h)$ of $L^2(\mathbb{R})$ and of $H^1(\mathbb{R})$.

## Main results

* `EllipticInterval.exists_contDiffMapIcc_of_continuous`: Step C, the $C^2$ part. A weak solution is
  $C^2$ when $f$, $\beta$, $\gamma$ are continuous and $\alpha$ is $C^1$ and does not vanish on
  $[a, b]$, and it is then a classical solution. The $H^2$ part of Step C is
  `EllipticInterval.mem_sobolevInterval_two_of_forall_testFunction` and
  `EllipticInterval.exists_sobolevInterval_two_of_forall_testFunction` in
  `Numlib.Variational.EllipticInterval`.
* `EllipticInterval.isClassicalSolution_of_contDiffMapIcc`: Step D. A $C^2$ weak solution is a
  classical solution. `EllipticInterval.isClassicalSolution_of_forall_testFunction` is the same from
  the weak equation tested against test functions only.
* `EllipticInterval.memSobolevInterval_add_two_of_isWeakSolution`: Remark 23. For the model problem,
  $f \in H^k$ implies $u \in H^{k+2}$.
* `EllipticInterval.modelForm_inclusionCLM_eq`: Green's formula for $\Phi \in H^2(a, b)$. All the
  uniqueness statements below follow from it.
* `EllipticInterval.natural_boundary_eq_of_forall`, with
  `EllipticInterval.natural_boundary_neumann`, `EllipticInterval.natural_boundary_mixed`,
  `EllipticInterval.natural_boundary_robin` and `EllipticInterval.natural_boundary_periodic`: a
  solution of a weak problem on a space $K \supseteq H^1_0(a, b)$ satisfies the equation and the
  natural boundary conditions that $K$ leaves free.
* `EllipticInterval.existsUnique_dirichletSet_of_variationalInequality`,
  `EllipticInterval.existsUnique_dirichlet_inhomogeneous`: Proposition 8.16, the inhomogeneous
  Dirichlet problem.
* `EllipticInterval.existsUnique_neumann`, `EllipticInterval.existsUnique_neumann_inhomogeneous`:
  Propositions 8.17 and 8.18, the Neumann problems.
* `EllipticInterval.existsUnique_mixed`, `EllipticInterval.existsUnique_robin`,
  `EllipticInterval.existsUnique_periodic`: Examples 5–7, the mixed, Robin and periodic problems.
* `EllipticInterval.Line.memSobolevIntervalLp_of_classical`,
  `EllipticInterval.Line.isWeakSolution_of_classical`: Example 8. A classical solution on
  $\mathbb{R}$ that tends to $0$ at infinity is in $H^1(\mathbb{R})$ and is the weak solution.
* `EllipticInterval.Line.exists_classical_solution`: for $f \in L^2(\mathbb{R}) \cap C(\mathbb{R})$,
  the problem on $\mathbb{R}$ has exactly one classical solution that tends to $0$ at infinity. By
  `EllipticInterval.Line.memSobolevIntervalLp_two_solution`, the weak solution is in
  $H^2(\mathbb{R})$.
* `EllipticInterval.Line.solution_translateLp`, `EllipticInterval.Line.solution_eq_zero_iff`,
  `EllipticInterval.Line.not_tendsto_translateLp`: the solution operator on $\mathbb{R}$ commutes
  with the translations and is injective, and the translates of a nonzero function of
  $L^2(\mathbb{R})$ have no convergent subsequence. These facts make the solution operator
  non-compact on $L^2(\mathbb{R})$, which is Remark 30 of Chapter 8 of [brezis2011functional].
  Remark 30 itself is stated in `NumlibSurface.Brezis.Chapter08.Section06`.

## Proof outline

Every strong problem is stated for $\Phi \in H^2(a, b)$, with the equation almost everywhere and the
boundary conditions on the continuous representatives. Existence comes from the Lax–Milgram theorem
(or the variational inequality, for the Dirichlet class), then Step C, then the recovery of the
natural boundary conditions. Uniqueness reduces through Green's formula to the uniqueness of the
weak solution, so no maximum principle is needed.

## Implementation notes

* All the problems on $(a, b)$ are posed on `SobolevInterval 1 a b`, which is $H^1(a, b)$. The form
  is `EllipticInterval.form a b α β γ`, with coefficients in $L^\infty(a, b)$, and the load is
  `EllipticInterval.load a b f`. The boundary functionals are `SobolevInterval.evalCLM`, the
  evaluations of the continuous representative `SobolevIntervalLp.rep`. The model form is
  `EllipticInterval.modelForm a b`, which is `EllipticInterval.form a b 1 0 1` and equals the inner
  product of $H^1(a, b)$ by `EllipticInterval.modelForm_eq_innerSL`.
* An $H^2$ conclusion is an element `Φ : SobolevInterval 2 a b` with
  `SobolevInterval.inclusionCLM 1 a b Φ = u`. Its second derivative is `SobolevInterval.deriv Φ 2`.
  The value $\Phi'(x)$ at an endpoint is the value at $x$ of the continuous representative
  `SobolevIntervalLp.rep` of `SobolevInterval.derivCLM 1 a b Φ`. Footnote 13 of the source observes
  that $u \in H^2$ gives a meaning to $u'(a)$ and $u'(b)$.
* "$u \in C^2[a, b]$" is an element `v : ContDiffMapIcc hab.le 2` of
  `Numlib.Analysis.Calculus.ContDiffMapIcc` with `EllipticInterval.ofContDiffMapIcc hab v = u`. "$v$
  is a classical solution" is the pointwise equation $-(\alpha v')'(x) + \beta(x) v'(x) + \gamma(x)
  v(x) = f(x)$ for every $x \in (a, b)$, as in `Numlib.Variational.EllipticInterval`.
* The regularity lemmas `EllipticInterval.mem_sobolevInterval_two_of_forall_testFunction` and
  `EllipticInterval.exists_sobolevInterval_two_of_forall_testFunction` of
  `Numlib.Variational.EllipticInterval` take the weak equation against $H^1_0(a, b)$ as the only
  hypothesis. They do not ask $u \in H^1_0(a, b)$, which Examples 1 and 3–8 do not have. The
  versions for $u \in H^1_0(a, b)$, such as
  `EllipticInterval.isWeakSolution_mem_sobolevInterval_two`, are special cases of them.
* The $C^2$ part of Step C goes through the continuous representative of $u' \in H^1$ and Remark 6
  of the source (`SobolevIntervalLp.contDiffOn_rep_of_continuousOn_deriv`), and not through the
  words "$(u')' \in C(\bar I)$, hence $u' \in C^1(\bar I)$" of the source. A $C^1$ coefficient
  $\alpha$ is handled by the flux identity $\alpha u'' = \beta u' + \gamma u - f - \alpha' u'$, so
  the Sturm–Liouville case of §8.6 needs no separate argument.
* Example 8 is posed on `SobolevIntervalLp 1 2 ⊤`, which is $H^1(\mathbb{R})$, from
  `Numlib.Analysis.Sobolev.Interval.Basic`. There the bilinear form is the inner product, and the
  Lax–Milgram theorem is the Riesz representation theorem. The translations are the whole-line cases
  of the isometries of `Numlib.Analysis.Sobolev.Translate`.
-/

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Topology InnerProductSpace

noncomputable section

/-! ### The continuous representative of a difference -/

section Bridge

variable {a b : ℝ}

/-- Let $a < b$ and $u, v \in H^1(a, b)$. The continuous representative of $u - v$ is the difference
of the continuous representatives of $u$ and $v$ on $[a, b]$. -/
theorem SobolevInterval.rep_sub (hab : a < b) (u v : SobolevInterval 1 a b) :
    EqOn (SobolevInterval.rep (u - v)) (SobolevInterval.rep u - SobolevInterval.rep v) (Icc a b) :=
  SobolevInterval.rep_eq_of_continuousOn hab (u - v)
    ((SobolevInterval.continuousOn_rep hab.le u).sub (SobolevInterval.continuousOn_rep hab.le v))
    ((Lp.coeFn_sub _ _).trans
      ((SobolevInterval.fn_ae_eq_rep u).sub (SobolevInterval.fn_ae_eq_rep v)))

end Bridge

namespace EllipticInterval

variable {a b : ℝ}

/-! ### Step C: the $C^2$ part -/

open SobolevInterval in
/-- Let $\Phi \in H^2(a, b)$ and $u \in H^1(a, b)$, with $u$ the inclusion of $\Phi$ in $H^1(a, b)$.
Then for $j = 0, 1$, the $j$-th weak derivative of $u$ is the $j$-th weak derivative of $\Phi$. -/
theorem deriv_inclusionCLM_eq {Φ : SobolevInterval 2 a b} {u : SobolevInterval 1 a b}
    (hΦ : inclusionCLM 1 a b Φ = u) (j : Fin 2) : deriv u j = deriv Φ j.castSucc := by
  rw [← hΦ, deriv_inclusionCLM]

open SobolevInterval in
/-- **Step C, the $C^2$ part.** Let $a < b$, let $\alpha, \beta, \gamma \in L^\infty(a, b)$ and
$f \in L^2(a, b)$, and let them agree almost everywhere on $(a, b)$ with functions, also written
$\alpha, \beta, \gamma, f$, such that $\alpha \in C^1[a, b]$, $\alpha(x) \neq 0$ for every
$x \in [a, b]$, and $\beta, \gamma, f$ are continuous on $[a, b]$. Let $u \in H^1(a, b)$ satisfy
$$\int_a^b (\alpha u' v' + \beta u' v + \gamma u v) = \int_a^b f v
  \quad \text{for every } v \in H^1_0(a, b).$$
Then there is $v \in C^2[a, b]$ that carries $u$, and
$$-(\alpha v')'(x) + \beta(x) v'(x) + \gamma(x) v(x) = f(x)
  \quad \text{for every } x \in (a, b).$$
This is part of Steps C and D in §8.4 of [brezis2011functional].

"$v$ carries $u$" is `EllipticInterval.ofContDiffMapIcc hab v = u`, so the continuous
representative of $u$ is $v$ on $[a, b]$. The proof: almost everywhere, $u'' = (\beta u' +
\gamma u - f - \alpha' u') / \alpha$, which is a function continuous on $[a, b]$. So $u'$ is
$C^1$ on $[a, b]$ by Remark 6 of the source
(`SobolevIntervalLp.contDiffOn_rep_of_continuousOn_deriv`), and so is $u$, with derivative $u'$. -/
theorem exists_contDiffMapIcc_of_continuous (hab : a < b)
    (αL βL γL : Lp ℝ ⊤ (volume.restrict (Ioo a b))) (fL : Lp ℝ 2 (volume.restrict (Ioo a b)))
    {α β γ f : ℝ → ℝ} (hαL : αL =ᵐ[volume.restrict (Ioo a b)] α)
    (hβL : βL =ᵐ[volume.restrict (Ioo a b)] β) (hγL : γL =ᵐ[volume.restrict (Ioo a b)] γ)
    (hfL : fL =ᵐ[volume.restrict (Ioo a b)] f) (hα : ContDiffOn ℝ 1 α (Icc a b))
    (hα0 : ∀ x ∈ Icc a b, α x ≠ 0) (hβ : ContinuousOn β (Icc a b))
    (hγ : ContinuousOn γ (Icc a b)) (hf : ContinuousOn f (Icc a b)) {u : SobolevInterval 1 a b}
    (hu : ∀ v ∈ SobolevIntervalZero a b, form a b αL βL γL u v = load a b fL v) :
    ∃ v : ContDiffMapIcc hab.le 2, ofContDiffMapIcc hab v = u ∧
      ∀ x ∈ Ioo a b, -_root_.deriv (fun t ↦ α t * v.shift.extend t) x
        + β x * v.shift.extend x + γ x * v.extend x = f x := by
  obtain ⟨Φ, hΦ, hae⟩ :=
    exists_sobolevInterval_two_of_forall_testFunction hab αL βL γL hαL hα hα0 fL hu
  set U₁ := derivCLM 1 a b Φ with hU₁def
  have hI := SobolevIntervalLp.ordConnected_coe_Ioo a b
  have hcl := SobolevIntervalLp.closure_coe_Ioo hab
  -- the representatives of `u'` and `u`
  have hU₁0 : (deriv U₁ 0 : ℝ → ℝ) = deriv u 1 := by
    rw [hU₁def, deriv_derivCLM, deriv_inclusionCLM_eq hΦ 1]; rfl
  have hU₁1 : deriv U₁ 1 = deriv Φ 2 := by rw [hU₁def, deriv_derivCLM]; rfl
  have hrepU₁ : (deriv u 1 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] SobolevIntervalLp.rep U₁ := by
    rw [← hU₁0]; exact SobolevIntervalLp.fn_ae_eq_rep hI U₁
  have hrepu : (deriv u 0 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] SobolevIntervalLp.rep u :=
    SobolevIntervalLp.fn_ae_eq_rep hI u
  -- `α'`, continuous on `[a, b]`
  have hα' : ContinuousOn (derivWithin α (Icc a b)) (Icc a b) :=
    hα.continuousOn_derivWithin (uniqueDiffOn_Icc hab) le_rfl
  have hαd : ∀ x ∈ Icc a b, HasDerivWithinAt α (derivWithin α (Icc a b) x) (Icc a b) x :=
    fun x hx ↦ ((hα.differentiableOn one_ne_zero) x hx).hasDerivWithinAt
  -- the continuous function `g = u''`
  set g : ℝ → ℝ := fun x ↦ (β x * SobolevIntervalLp.rep U₁ x + γ x * SobolevIntervalLp.rep u x
    - f x - derivWithin α (Icc a b) x * SobolevIntervalLp.rep U₁ x) / α x with hgdef
  have hcU₁ : ContinuousOn (SobolevIntervalLp.rep U₁) (Icc a b) :=
    SobolevIntervalLp.continuousOn_rep_Icc hab U₁
  have hcu : ContinuousOn (SobolevIntervalLp.rep u) (Icc a b) :=
    SobolevIntervalLp.continuousOn_rep_Icc hab u
  have hgc : ContinuousOn g (Icc a b) :=
    (((hβ.mul hcU₁).add (hγ.mul hcu)).sub hf |>.sub (hα'.mul hcU₁)).div hα.continuousOn hα0
  have hgae : (deriv U₁ 1 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] g := by
    rw [hU₁1]
    filter_upwards [hae, hβL, hγL, hfL, hrepU₁, hrepu, ae_restrict_mem measurableSet_Ioo]
      with x h1 h2 h3 h4 h5 h6 hx
    have hx' := Ioo_subset_Icc_self hx
    rw [h2, h3, h4, h5, h6] at h1
    rw [hgdef]
    dsimp only
    rw [← h1]
    field_simp [hα0 x hx']
  -- `u' ∈ C¹[a, b]` with derivative `g`, and `u ∈ C¹[a, b]` with derivative `u'`
  have h1 := SobolevIntervalLp.contDiffOn_rep_of_continuousOn_deriv hI U₁ (g := g)
    (by rw [hcl]; exact hgc) hgae
  rw [hcl] at h1
  have h0 := SobolevIntervalLp.contDiffOn_rep_of_continuousOn_deriv hI u
    (g := SobolevIntervalLp.rep U₁) (by rw [hcl]; exact hcU₁) hrepU₁
  rw [hcl] at h0
  have hdw : ∀ x ∈ Icc a b, derivWithin (SobolevIntervalLp.rep u) (Icc a b) x
      = SobolevIntervalLp.rep U₁ x := fun x hx ↦
    (h0.2 x hx).derivWithin (uniqueDiffOn_Icc hab x hx)
  have hC2 : ContDiffOn ℝ ((2 : ℕ) : ℕ∞ω) (SobolevIntervalLp.rep u) (Icc a b) := by
    rw [show ((2 : ℕ) : ℕ∞ω) = (1 : ℕ∞ω) + 1 by norm_num,
      contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hab)]
    exact ⟨fun x hx ↦ (h0.2 x hx).differentiableWithinAt, fun h ↦ absurd h (by simp),
      h1.1.congr fun x hx ↦ hdw x hx⟩
  set v := ContDiffMapIcc.ofContDiffOn hab.le hab hC2 with hvdef
  have hv0 : ∀ x ∈ Icc a b, v.extend x = SobolevIntervalLp.rep u x := fun x hx ↦ by
    rw [ContDiffMapIcc.extend_of_mem v hx, hvdef]
    exact ContDiffMapIcc.coe_ofContDiffOn hab.le hab hC2 ⟨x, hx⟩
  have hv1 : ∀ x ∈ Icc a b, v.shift.extend x = SobolevIntervalLp.rep U₁ x := fun x hx ↦ by
    rw [ContDiffMapIcc.extend_of_mem v.shift hx]
    change v.shift.deriv 0 ⟨x, hx⟩ = _
    rw [ContDiffMapIcc.deriv_shift, hvdef, ContDiffMapIcc.deriv_ofContDiffOn]
    change iteratedDerivWithin 1 (SobolevIntervalLp.rep u) (Icc a b) x = _
    rw [iteratedDerivWithin_one, hdw x hx]
  refine ⟨v, ?_, fun x hx ↦ ?_⟩
  · refine SobolevMultiIndex.ext_of_fn_ae_eq ?_
    refine (deriv_ofContDiffMapIcc_zero hab v).trans ?_
    filter_upwards [hrepu, ae_restrict_mem measurableSet_Ioo] with x h hx
    rw [hv0 x (Ioo_subset_Icc_self hx)]
    exact h.symm
  · have hx' := Ioo_subset_Icc_self hx
    have hnhds : Icc a b ∈ 𝓝 x := Icc_mem_nhds hx.1 hx.2
    -- the derivative of the flux `α v'` at `x`
    have hflux : HasDerivAt (fun t ↦ α t * v.shift.extend t)
        (derivWithin α (Icc a b) x * SobolevIntervalLp.rep U₁ x + α x * g x) x := by
      have := ((hαd x hx').mul (h1.2 x hx')).hasDerivAt hnhds
      refine this.congr_of_eventuallyEq ?_
      filter_upwards [hnhds] with t ht
      rw [hv1 t ht]; rfl
    rw [hflux.deriv, hv1 x hx', hv0 x hx', hgdef]
    dsimp only
    field_simp [hα0 x hx']
    ring

/-! ### Step D: a $C^2$ weak solution is a classical solution -/

/-- **The step from almost everywhere to everywhere in Step D.** Let $a < b$, let
$\alpha \in C^1[a, b]$, let $\beta, \gamma, f$ be continuous on $[a, b]$, and let
$v \in C^2[a, b]$. If the flux $\alpha v'$ has the weak derivative $\beta v' + \gamma v - f$ on
$(a, b)$, then
$$-(\alpha v')'(x) + \beta(x) v'(x) + \gamma(x) v(x) = f(x)
  \quad \text{for every } x \in (a, b).$$

The classical and the weak derivative of the flux agree almost everywhere, and both sides are
continuous. -/
theorem forall_ode_of_hasWeakDerivOn (hab : a < b) {α β γ f : ℝ → ℝ}
    (hα : ContDiffOn ℝ 1 α (Icc a b)) (hβ : ContinuousOn β (Icc a b))
    (hγ : ContinuousOn γ (Icc a b)) (hf : ContinuousOn f (Icc a b)) (v : ContDiffMapIcc hab.le 2)
    (hw : HasWeakDerivOn (fun x ↦ α x * v.shift.extend x)
      (fun x ↦ β x * v.shift.extend x + γ x * v.extend x - f x) (Opens.Ioo a b)) :
    ∀ x ∈ Ioo a b, -_root_.deriv (fun t ↦ α t * v.shift.extend t) x
      + β x * v.shift.extend x + γ x * v.extend x = f x := by
  set ψ : ℝ → ℝ := fun t ↦ α t * v.shift.extend t with hψ
  have hu1 : ContDiffOn ℝ 1 v.shift.extend (Icc a b) := v.shift.contDiffOn hab
  have hψc : ContDiffOn ℝ 1 ψ (Icc a b) := hα.mul hu1
  have hclass : HasWeakDerivOn ψ (_root_.deriv ψ) (Opens.Ioo a b) :=
    hasWeakDerivOn_of_contDiffOn (I := Opens.Ioo a b) (hψc.mono Ioo_subset_Icc_self)
  have hae := hw.ae_eq hclass
  set d := derivWithin ψ (Icc a b) with hd
  have hdc : ContinuousOn d (Icc a b) :=
    hψc.continuousOn_derivWithin (uniqueDiffOn_Icc hab) le_rfl
  have hdd : ∀ x ∈ Ioo a b, d x = _root_.deriv ψ x := fun x hx ↦
    derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)
  have hlhs : ContinuousOn (fun x ↦ β x * v.shift.extend x + γ x * v.extend x - f x)
      (Icc a b) :=
    ((hβ.mul hu1.continuousOn).add (hγ.mul v.extend.continuous.continuousOn)).sub hf
  have heq := eqOn_Icc_of_ae_eq hab hlhs hdc (by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hae] with x hx hxI
    rw [hx hxI, hdd x hxI])
  intro x hx
  have := heq (Ioo_subset_Icc_self hx)
  rw [hdd x hx] at this
  simp only at this
  linarith

/-- **Step D: a $C^2$ weak solution is a classical solution.** Let $a < b$, let
$\alpha, \beta, \gamma \in L^\infty(a, b)$ and $f \in L^2(a, b)$, and let them agree almost
everywhere on $(a, b)$ with functions $\alpha \in C^1[a, b]$ and $\beta, \gamma, f$ continuous
on $[a, b]$. Let $v \in C^2[a, b]$ satisfy
$$\int_a^b (\alpha v' w' + \beta v' w + \gamma v w) = \int_a^b f w
  \quad \text{for every } w \in H^1_0(a, b).$$
Then $-(\alpha v')' + \beta v' + \gamma v = f$ at every point of $(a, b)$. This is part of §8.1
of [brezis2011functional], and the converse of `EllipticInterval.isWeakSolution_of_classical`. -/
theorem isClassicalSolution_of_contDiffMapIcc (hab : a < b)
    (αL βL γL : Lp ℝ ⊤ (volume.restrict (Ioo a b))) (fL : Lp ℝ 2 (volume.restrict (Ioo a b)))
    {α β γ f : ℝ → ℝ} (hαL : αL =ᵐ[volume.restrict (Ioo a b)] α)
    (hβL : βL =ᵐ[volume.restrict (Ioo a b)] β) (hγL : γL =ᵐ[volume.restrict (Ioo a b)] γ)
    (hfL : fL =ᵐ[volume.restrict (Ioo a b)] f) (hα : ContDiffOn ℝ 1 α (Icc a b))
    (hβ : ContinuousOn β (Icc a b)) (hγ : ContinuousOn γ (Icc a b))
    (hf : ContinuousOn f (Icc a b)) (v : ContDiffMapIcc hab.le 2)
    (hv : ∀ w ∈ SobolevIntervalZero a b,
      form a b αL βL γL (ofContDiffMapIcc hab v) w = load a b fL w) :
    ∀ x ∈ Ioo a b, -_root_.deriv (fun t ↦ α t * v.shift.extend t) x
      + β x * v.shift.extend x + γ x * v.extend x = f x := by
  refine forall_ode_of_hasWeakDerivOn hab hα hβ hγ hf v ?_
  refine (hasWeakDerivOn_mulL_deriv_of_forall αL βL γL fL hv).congr_ae ?_ ?_
  · filter_upwards [hαL, deriv_ofContDiffMapIcc_one hab v] with x h1 h2
    rw [h1, h2]
  · filter_upwards [hβL, hγL, hfL, deriv_ofContDiffMapIcc_one hab v,
      deriv_ofContDiffMapIcc_zero hab v] with x h1 h2 h3 h4 h5
    rw [h1, h2, h3, h4, h5]

/-- A function continuous on $[a, b]$ is locally integrable on $(a, b)$. -/
theorem _root_.ContinuousOn.locallyIntegrableOn_Ioo {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc a b)) : LocallyIntegrableOn g (Ioo a b) :=
  (hg.integrableOn_Icc.mono_set Ioo_subset_Icc_self).locallyIntegrableOn

/-- **Step D from the test functions only.** Let $a < b$, let $\alpha \in C^1[a, b]$, let
$\beta, \gamma, f$ be continuous on $[a, b]$, and let $v \in C^2[a, b]$ satisfy
$$\int_a^b (\alpha v' \varphi' + \beta v' \varphi + \gamma v \varphi) = \int_a^b f \varphi
  \quad \text{for every } \varphi \in C_c^\infty((a, b)).$$
Then $-(\alpha v')' + \beta v' + \gamma v = f$ at every point of $(a, b)$. This is the
derivation in §8.1 of [brezis2011functional] of $-u'' + u = f$ almost everywhere from equation
(2).

The provisional weak solutions of §8.1, which are tested against $C^1$ functions that vanish at
the endpoints, reduce to this form. -/
theorem isClassicalSolution_of_forall_testFunction (hab : a < b) {α β γ f : ℝ → ℝ}
    (hα : ContDiffOn ℝ 1 α (Icc a b)) (hβ : ContinuousOn β (Icc a b))
    (hγ : ContinuousOn γ (Icc a b)) (hf : ContinuousOn f (Icc a b)) (v : ContDiffMapIcc hab.le 2)
    (hv : ∀ φ : 𝓓(Opens.Ioo a b, ℝ), ∫ x in Ioo a b, (α x * v.shift.extend x * _root_.deriv φ x
      + β x * v.shift.extend x * φ x + γ x * v.extend x * φ x) = ∫ x in Ioo a b, f x * φ x) :
    ∀ x ∈ Ioo a b, -_root_.deriv (fun t ↦ α t * v.shift.extend t) x
      + β x * v.shift.extend x + γ x * v.extend x = f x := by
  refine forall_ode_of_hasWeakDerivOn hab hα hβ hγ hf v ?_
  have hu1 : ContinuousOn v.shift.extend (Icc a b) := v.shift.extend.continuous.continuousOn
  have hu0 : ContinuousOn v.extend (Icc a b) := v.extend.continuous.continuousOn
  have hc1 : ContinuousOn (fun x ↦ α x * v.shift.extend x) (Icc a b) := hα.continuousOn.mul hu1
  have hc2 : ContinuousOn (fun x ↦ β x * v.shift.extend x + γ x * v.extend x - f x) (Icc a b) :=
    ((hβ.mul hu1).add (hγ.mul hu0)).sub hf
  refine hasWeakDerivOn_iff.2 ⟨hc1.locallyIntegrableOn_Ioo, hc2.locallyIntegrableOn_Ioo,
    fun φ ↦ ?_⟩
  rw [Opens.coe_Ioo]
  have hφ : ContinuousOn (φ : ℝ → ℝ) (Icc a b) := φ.continuous.continuousOn
  have hφ' : ContinuousOn (_root_.deriv φ) (Icc a b) := (φ.fderivApply 1).continuous.continuousOn
  have i1 : IntegrableOn (fun x ↦ _root_.deriv φ x * (α x * v.shift.extend x)) (Ioo a b) :=
    (hφ'.mul hc1).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have i2 : IntegrableOn (fun x ↦ φ x * (β x * v.shift.extend x + γ x * v.extend x)) (Ioo a b) :=
    (hφ.mul ((hβ.mul hu1).add (hγ.mul hu0))).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have i3 : IntegrableOn (fun x ↦ φ x * f x) (Ioo a b) :=
    (hφ.mul hf).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have key := hv φ
  have e1 : ∫ x in Ioo a b, (α x * v.shift.extend x * _root_.deriv φ x
      + β x * v.shift.extend x * φ x + γ x * v.extend x * φ x) = ∫ x in Ioo a b,
        (_root_.deriv φ x * (α x * v.shift.extend x)
          + φ x * (β x * v.shift.extend x + γ x * v.extend x)) :=
    integral_congr_ae (Eventually.of_forall fun x ↦ by simp only; ring)
  have e2 : ∫ x in Ioo a b, f x * φ x = ∫ x in Ioo a b, φ x * f x :=
    integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
  rw [e1, e2, integral_add i1 i2] at key
  have e3 : ∫ x in Ioo a b, φ x * (β x * v.shift.extend x + γ x * v.extend x - f x)
      = (∫ x in Ioo a b, φ x * (β x * v.shift.extend x + γ x * v.extend x))
        - ∫ x in Ioo a b, φ x * f x := by
    rw [← integral_sub i2 i3]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only; ring)
  rw [e3]
  linarith

/-! ### Remark 23: higher regularity for the model problem -/

/-- If $g$ and $h$ are in $H^k(a, b)$, then $g - h$ is in $H^k(a, b)$. -/
theorem _root_.MemSobolevInterval.sub {k : ℕ} {g h : ℝ → ℝ} (hg : MemSobolevInterval g k a b)
    (hh : MemSobolevInterval h k a b) : MemSobolevInterval (fun x ↦ g x - h x) k a b := by
  obtain ⟨G, hG⟩ := MemSobolevMultiIndex.exists_sobolevMultiIndex hg
  obtain ⟨H, hH⟩ := MemSobolevMultiIndex.exists_sobolevMultiIndex hh
  refine (SobolevIntervalLp.memSobolevIntervalLp_fn (G - H)).congr_ae ?_
  have e : SobolevInterval.fn (G - H) =ᵐ[volume.restrict (Ioo a b)]
      SobolevInterval.fn G - SobolevInterval.fn H := Lp.coeFn_sub _ _
  filter_upwards [e, hG, hH] with x h1 h2 h3
  rw [h1, Pi.sub_apply]
  change SobolevMultiIndex.fn G x - SobolevMultiIndex.fn H x = _
  rw [h2, h3]

open SobolevInterval in
/-- Let $f \in L^2(a, b)$, and let $u \in H^1(a, b)$ satisfy $\int_a^b (u' v' + u v) = \int_a^b f v$
for every $v \in H^1_0(a, b)$. Then $u'$ has the weak derivative $u - f$ on $(a, b)$.

This is `EllipticInterval.hasWeakDerivOn_mulL_deriv_of_forall` for $\alpha = \gamma = 1$ and
$\beta = 0$. -/
theorem hasWeakDerivOn_deriv_of_forall_modelForm (f : Lp ℝ 2 (volume.restrict (Ioo a b)))
    {u : SobolevInterval 1 a b}
    (hu : ∀ v ∈ SobolevIntervalZero a b, modelForm a b u v = load a b f v) :
    HasWeakDerivOn (deriv u 1) (fun x ↦ fn u x - f x) (Opens.Ioo a b) := by
  refine (hasWeakDerivOn_mulL_deriv_of_forall _ _ _ f hu).congr_ae ?_ ?_
  · filter_upwards [coeFn_constLinf a b 1] with x h1
    rw [h1, one_mul]
  · filter_upwards [coeFn_constLinf a b 1, Lp.coeFn_zero ℝ ⊤ (volume.restrict (Ioo a b))]
      with x h1 h2
    rw [h1, h2, Pi.zero_apply, zero_mul, one_mul, zero_add, deriv_zero]

open SobolevInterval in
/-- **Higher regularity for the model problem.** Let $f \in L^2(a, b)$, and let $u \in H^1(a, b)$
satisfy
$$\int_a^b (u' v' + u v) = \int_a^b f v \quad \text{for every } v \in H^1_0(a, b).$$
If $f \in H^k(a, b)$ for some $k \in \mathbb{N}$, then $u \in H^{k+2}(a, b)$. This is Remark 23
of [brezis2011functional].

The proof is by induction on $k$: $u'' = u - f$ weakly, and $u - f \in H^{k+1}$ once
$u \in H^{k+2}$. -/
theorem memSobolevInterval_add_two_of_isWeakSolution
    (f : Lp ℝ 2 (volume.restrict (Ioo a b))) {u : SobolevInterval 1 a b}
    (hu : ∀ v ∈ SobolevIntervalZero a b, modelForm a b u v = load a b f v) {k : ℕ}
    (hf : MemSobolevInterval f k a b) : MemSobolevInterval (fn u) (k + 2) a b := by
  have hw := hasWeakDerivOn_deriv_of_forall_modelForm f hu
  induction k with
  | zero =>
    refine memSobolevInterval_succ_iff.2 ⟨Lp.memLp _, deriv u 1, hasWeakDerivOn_fn u, ?_⟩
    exact memSobolevInterval_one_iff.2 ⟨Lp.memLp _, _, hw, (Lp.memLp (deriv u 0)).sub (Lp.memLp f)⟩
  | succ k ih =>
    have hu2 := ih (hf.mono_order (Nat.le_succ k))
    refine memSobolevInterval_succ_iff.2 ⟨Lp.memLp _, deriv u 1, hasWeakDerivOn_fn u, ?_⟩
    refine memSobolevInterval_succ_iff.2 ⟨Lp.memLp _, _, hw, ?_⟩
    exact _root_.MemSobolevInterval.sub
      (hu2.mono_order (Nat.le_succ (k + 1)) : MemSobolevInterval (fn u) (k + 1) a b) hf

/-! ### Green's formula for $H^2(a, b)$, and the natural boundary conditions -/

open SobolevInterval in
/-- **Green's formula for $\Phi \in H^2(a, b)$.** Let $a < b$, $\Phi \in H^2(a, b)$ and
$v \in H^1(a, b)$. Then
$$\int_a^b (\Phi' v' + \Phi v) = \int_a^b (\Phi - \Phi'') v + \Phi'(b) v(b) - \Phi'(a) v(a).$$
This is the identity (23) in the proof of Proposition 8.17 of [brezis2011functional].

Here $\Phi'(x)$ is the value of the continuous representative of $\Phi' \in H^1(a, b)$, and $v$
in the integral is the continuous representative of $v$. -/
theorem modelForm_inclusionCLM_eq (hab : a < b) (Φ : SobolevInterval 2 a b)
    (v : SobolevInterval 1 a b) :
    modelForm a b (inclusionCLM 1 a b Φ) v
      = (∫ x in Ioo a b, (fn Φ x - deriv Φ 2 x) * rep v x)
        + (rep (derivCLM 1 a b Φ) b * rep v b - rep (derivCLM 1 a b Φ) a * rep v a) := by
  set U₁ := derivCLM 1 a b Φ with hU₁def
  have hU₁0 : deriv U₁ 0 = deriv Φ 1 := by rw [hU₁def, deriv_derivCLM]; rfl
  have hU₁1 : deriv U₁ 1 = deriv Φ 2 := by rw [hU₁def, deriv_derivCLM]; rfl
  have green := integral_deriv_mul_add_mul_deriv hab U₁ v
  rw [intervalIntegral.integral_eq_setIntegral_Ioo hab.le] at green
  have i1 : IntegrableOn (fun t ↦ deriv U₁ 1 t * rep v t) (Ioo a b) :=
    (SobolevIntervalLp.integrableOn_deriv_Ioo U₁ 1).mul_continuousOn_of_subset
      (continuousOn_rep hab.le v)
      measurableSet_Ioo isCompact_Icc Ioo_subset_Icc_self
  have i2 : IntegrableOn (fun t ↦ rep U₁ t * deriv v 1 t) (Ioo a b) :=
    (SobolevIntervalLp.integrableOn_deriv_Ioo v 1).continuousOn_mul_of_subset
      (continuousOn_rep hab.le U₁)
      isCompact_Icc measurableSet_Ioo Ioo_subset_Icc_self
  rw [integral_add i1 i2] at green
  -- the form as two integrals
  have e0 : modelForm a b (inclusionCLM 1 a b Φ) v
      = (∫ x in Ioo a b, rep U₁ x * deriv v 1 x) + ∫ x in Ioo a b, fn Φ x * rep v x := by
    rw [modelForm_apply, inner_eq, Fin.sum_univ_two, deriv_inclusionCLM, deriv_inclusionCLM,
      show Fin.castSucc (1 : Fin 2) = (1 : Fin 3) from rfl,
      show Fin.castSucc (0 : Fin 2) = (0 : Fin 3) from rfl, ← hU₁0, L2.inner_def, L2.inner_def,
      add_comm]
    congr 1
    · refine integral_congr_ae ?_
      filter_upwards [fn_ae_eq_rep U₁] with x hx
      have hx' : (deriv U₁ 0 : ℝ → ℝ) x = rep U₁ x := hx
      simp only [RCLike.inner_apply, conj_trivial]
      rw [hx', mul_comm]
    · refine integral_congr_ae ?_
      filter_upwards [fn_ae_eq_rep v] with x hx
      have hx' : (deriv v 0 : ℝ → ℝ) x = rep v x := hx
      simp only [RCLike.inner_apply, conj_trivial]
      rw [hx', mul_comm]
      rfl
  have i3 : IntegrableOn (fun t ↦ fn Φ t * rep v t) (Ioo a b) :=
    (SobolevIntervalLp.integrableOn_deriv_Ioo Φ 0).mul_continuousOn_of_subset
      (continuousOn_rep hab.le v)
      measurableSet_Ioo isCompact_Icc Ioo_subset_Icc_self
  have i4 : IntegrableOn (fun t ↦ deriv Φ 2 t * rep v t) (Ioo a b) :=
    (SobolevIntervalLp.integrableOn_deriv_Ioo Φ 2).mul_continuousOn_of_subset
      (continuousOn_rep hab.le v)
      measurableSet_Ioo isCompact_Icc Ioo_subset_Icc_self
  have e1 : ∫ x in Ioo a b, (fn Φ x - deriv Φ 2 x) * rep v x
      = (∫ x in Ioo a b, fn Φ x * rep v x) - ∫ x in Ioo a b, deriv Φ 2 x * rep v x := by
    rw [← integral_sub i3 i4]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only; ring)
  rw [e0, e1, ← hU₁1]
  linarith

open SobolevInterval in
/-- **Green's formula for a solution of the model equation.** Let $a < b$, $f \in L^2(a, b)$, and
let $\Phi \in H^2(a, b)$ satisfy $-\Phi'' + \Phi = f$ almost everywhere on $(a, b)$. Then for
every $v \in H^1(a, b)$,
$$\int_a^b (\Phi' v' + \Phi v) = \int_a^b f v + \Phi'(b) v(b) - \Phi'(a) v(a).$$
-/
theorem modelForm_inclusionCLM_eq_of_deriv_two (hab : a < b)
    (f : Lp ℝ 2 (volume.restrict (Ioo a b))) {Φ : SobolevInterval 2 a b}
    (hΦ : (deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] fun x ↦ fn Φ x - f x)
    (v : SobolevInterval 1 a b) :
    modelForm a b (inclusionCLM 1 a b Φ) v
      = load a b f v
        + (rep (derivCLM 1 a b Φ) b * rep v b - rep (derivCLM 1 a b Φ) a * rep v a) := by
  rw [modelForm_inclusionCLM_eq hab Φ v, load_apply]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hΦ, fn_ae_eq_rep v] with x h1 h2
  rw [h1, deriv_zero, h2]
  ring

open SobolevInterval in
/-- Let $a < b$, $f \in L^2(a, b)$, and let $\Phi \in H^2(a, b)$ satisfy $-\Phi'' + \Phi = f$ almost
everywhere on $(a, b)$, whatever its boundary values. Then
$\int_a^b (\Phi' v' + \Phi v) = \int_a^b f v$ for every $v \in H^1_0(a, b)$.

The boundary terms of Green's formula vanish. -/
theorem modelForm_inclusionCLM_eq_load_of_mem (hab : a < b)
    (f : Lp ℝ 2 (volume.restrict (Ioo a b))) {Φ : SobolevInterval 2 a b}
    (hΦ : (deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] fun x ↦ fn Φ x - f x)
    {v : SobolevInterval 1 a b} (hv : v ∈ SobolevIntervalZero a b) :
    modelForm a b (inclusionCLM 1 a b Φ) v = load a b f v := by
  rw [modelForm_inclusionCLM_eq_of_deriv_two hab f hΦ v,
    SobolevIntervalZero.rep_left_eq_zero hab hv, SobolevIntervalZero.rep_right_eq_zero hab hv]
  ring

open SobolevInterval in
/-- Two elements of $H^2(a, b)$ with the same inclusion in $H^1(a, b)$ and the same second
derivative are equal. -/
theorem sobolevInterval_two_ext {Φ₁ Φ₂ : SobolevInterval 2 a b}
    (h : inclusionCLM 1 a b Φ₁ = inclusionCLM 1 a b Φ₂) (h2 : deriv Φ₁ 2 = deriv Φ₂ 2) :
    Φ₁ = Φ₂ := by
  refine ext fun j ↦ ?_
  fin_cases j
  · exact (deriv_inclusionCLM Φ₁ 0).symm.trans
      ((congrArg (SobolevInterval.deriv · 0) h).trans (deriv_inclusionCLM Φ₂ 0))
  · exact (deriv_inclusionCLM Φ₁ 1).symm.trans
      ((congrArg (SobolevInterval.deriv · 1) h).trans (deriv_inclusionCLM Φ₂ 1))
  · exact h2

open SobolevInterval in
/-- Let $f \in L^2(a, b)$. Two elements $\Phi_1, \Phi_2 \in H^2(a, b)$ that satisfy
$-\Phi_i'' + \Phi_i = f$ almost everywhere on $(a, b)$ and have the same inclusion in
$H^1(a, b)$ are equal. -/
theorem eq_of_inclusionCLM_eq_of_deriv_two (f : Lp ℝ 2 (volume.restrict (Ioo a b)))
    {Φ₁ Φ₂ : SobolevInterval 2 a b}
    (h₁ : (deriv Φ₁ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] fun x ↦ fn Φ₁ x - f x)
    (h₂ : (deriv Φ₂ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] fun x ↦ fn Φ₂ x - f x)
    (h : inclusionCLM 1 a b Φ₁ = inclusionCLM 1 a b Φ₂) : Φ₁ = Φ₂ := by
  refine sobolevInterval_two_ext h (Lp.ext ?_)
  have hfn : fn Φ₁ = fn Φ₂ := by
    rw [← fn_inclusionCLM Φ₁, h, fn_inclusionCLM]
  refine h₁.trans (EventuallyEq.trans ?_ h₂.symm)
  rw [hfn]

open SobolevInterval in
/-- **Step C for the model problem.** Let $f \in L^2(a, b)$, and let $u \in H^1(a, b)$ satisfy
$\int_a^b (u' v' + u v) = \int_a^b f v$ for every $v \in H^1_0(a, b)$. Then $u$ is the inclusion
of some $\Phi \in H^2(a, b)$ with $-\Phi'' + \Phi = f$ almost everywhere on $(a, b)$. -/
theorem exists_sobolevInterval_two_of_forall_modelForm
    (f : Lp ℝ 2 (volume.restrict (Ioo a b))) {u : SobolevInterval 1 a b}
    (hu : ∀ v ∈ SobolevIntervalZero a b, modelForm a b u v = load a b f v) :
    ∃ Φ : SobolevInterval 2 a b, inclusionCLM 1 a b Φ = u ∧
      (deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] fun x ↦ fn Φ x - f x := by
  have hw := hasWeakDerivOn_deriv_of_forall_modelForm f hu
  obtain ⟨U₁, hU₁⟩ := MemSobolevMultiIndex.exists_sobolevMultiIndex
    (memSobolevInterval_one_iff.2 ⟨Lp.memLp _, _, hw, (Lp.memLp (deriv u 0)).sub (Lp.memLp f)⟩)
  obtain ⟨Φ, hΦ, hΦ2⟩ := exists_sobolevInterval_two u U₁ hU₁
  refine ⟨Φ, hΦ, ?_⟩
  rw [hΦ2]
  have h1 : HasWeakDerivOn (fn U₁) (deriv U₁ 1) (Opens.Ioo a b) := hasWeakDerivOn_fn U₁
  have h2 : HasWeakDerivOn (fn U₁) (fun x ↦ fn u x - f x) (Opens.Ioo a b) :=
    hw.congr_ae hU₁.symm EventuallyEq.rfl
  have := (ae_restrict_iff' measurableSet_Ioo).2 (h1.ae_eq h2)
  filter_upwards [this] with x hx
  rw [hx, ← fn_inclusionCLM Φ, hΦ]

open SobolevInterval in
/-- **Recovery of the natural boundary conditions.** Let $a < b$, $f \in L^2(a, b)$,
$w_0, w_1 \in \mathbb{R}$, and let $K$ be a subspace of $H^1(a, b)$ that contains $H^1_0(a, b)$.
Let $\Phi \in H^2(a, b)$ satisfy
$$\int_a^b (\Phi' v' + \Phi v) = \int_a^b f v + w_1 v(b) - w_0 v(a)
  \quad \text{for every } v \in K.$$
Then

* $-\Phi'' + \Phi = f$ almost everywhere on $(a, b)$, and
* $(\Phi'(b) - w_1) v(b) = (\Phi'(a) - w_0) v(a)$ for every $v \in K$.

This is the common step of Examples 3–7 and Propositions 8.17–8.18 of [brezis2011functional].
The choice of $K$ and of $v$ then gives the Neumann, mixed, Robin and periodic conditions. -/
theorem natural_boundary_eq_of_forall (hab : a < b) (f : Lp ℝ 2 (volume.restrict (Ioo a b)))
    {w₀ w₁ : ℝ} {K : Submodule ℝ (SobolevInterval 1 a b)} (hK : SobolevIntervalZero a b ≤ K)
    (Φ : SobolevInterval 2 a b) (h : ∀ v ∈ K, modelForm a b (inclusionCLM 1 a b Φ) v
      = load a b f v + w₁ * rep v b - w₀ * rep v a) :
    ((deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] fun x ↦ fn Φ x - f x) ∧
      ∀ v ∈ K, (rep (derivCLM 1 a b Φ) b - w₁) * rep v b
        = (rep (derivCLM 1 a b Φ) a - w₀) * rep v a := by
  have h0 : ∀ v ∈ SobolevIntervalZero a b, modelForm a b (inclusionCLM 1 a b Φ) v
      = load a b f v := fun v hv ↦ by
    rw [h v (hK hv), SobolevIntervalZero.rep_left_eq_zero hab hv,
      SobolevIntervalZero.rep_right_eq_zero hab hv]
    ring
  have heq : (deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] fun x ↦ fn Φ x - f x := by
    have hw := hasWeakDerivOn_deriv_of_forall_modelForm f h0
    rw [deriv_inclusionCLM_eq rfl 1, fn_inclusionCLM] at hw
    have h1 : HasWeakDerivOn (deriv Φ 1) (deriv Φ 2) (Opens.Ioo a b) :=
      hasWeakDerivOn_deriv_succ Φ 1
    exact (ae_restrict_iff' measurableSet_Ioo).2 (h1.ae_eq hw)
  refine ⟨heq, fun v hv ↦ ?_⟩
  have := h v hv
  rw [modelForm_inclusionCLM_eq_of_deriv_two hab f heq v] at this
  linarith

/-! ### The affine lift, the Dirichlet class, and the spaces of Examples 5–7 -/

open SobolevInterval in
/-- **The affine lift**: for $a < b$, $m \in \mathbb{N}$ and $\alpha, \beta \in \mathbb{R}$, the
affine function
$$x \mapsto \alpha + (\beta - \alpha) \frac{x - a}{b - a},$$
as an element of $H^m(a, b)$. It takes the value $\alpha$ at $a$ and $\beta$ at $b$.

It is the smooth lift $u_0$ of Example 1, Method 1, in §8.4 of [brezis2011functional]. Footnote
12 of the source says that $u_0$ can be taken affine. -/
def affineLift (hab : a < b) (m : ℕ) (α β : ℝ) : SobolevInterval m a b :=
  ContDiffMapIcc.toSobolevInterval hab.le hab m (ContDiffMapIcc.ofContDiff hab.le
    (show ContDiff ℝ m fun x ↦ α + (β - α) * ((x - a) / (b - a)) by fun_prop))

open SobolevInterval in
/-- The function of the affine lift is the affine function $x \mapsto \alpha + (\beta - \alpha)(x -
a)/(b - a)$, almost everywhere on $(a, b)$. -/
theorem fn_affineLift_ae_eq (hab : a < b) (m : ℕ) (α β : ℝ) :
    fn (affineLift hab m α β) =ᵐ[volume.restrict (Ioo a b)]
      fun x ↦ α + (β - α) * ((x - a) / (b - a)) := by
  refine (ContDiffMapIcc.fn_toSobolevInterval_ae_eq hab.le hab _).trans ?_
  refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx ↦ ?_)
  rw [ContDiffMapIcc.extend_of_mem _ (Ioo_subset_Icc_self hx)]
  exact ContDiffMapIcc.coe_ofContDiff hab.le _ ⟨x, Ioo_subset_Icc_self hx⟩

open SobolevInterval in
/-- The continuous representative of the affine lift in $H^1(a, b)$ is the affine function $x
\mapsto \alpha + (\beta - \alpha)(x - a)/(b - a)$ on $[a, b]$. -/
theorem rep_affineLift (hab : a < b) (α β : ℝ) :
    EqOn (rep (affineLift hab 1 α β)) (fun x ↦ α + (β - α) * ((x - a) / (b - a))) (Icc a b) :=
  rep_eq_of_continuousOn hab _ (by fun_prop) (fn_affineLift_ae_eq hab 1 α β)

open SobolevInterval in
/-- The affine lift takes the value $\alpha$ at $a$. -/
theorem rep_affineLift_left (hab : a < b) (α β : ℝ) : rep (affineLift hab 1 α β) a = α := by
  rw [rep_affineLift hab α β (left_mem_Icc.2 hab.le)]
  simp

open SobolevInterval in
/-- The affine lift takes the value $\beta$ at $b$. -/
theorem rep_affineLift_right (hab : a < b) (α β : ℝ) : rep (affineLift hab 1 α β) b = β := by
  rw [rep_affineLift hab α β (right_mem_Icc.2 hab.le)]
  simp only
  rw [div_self (sub_pos.2 hab).ne', mul_one]
  ring

open SobolevInterval in
/-- The inclusion in $H^1(a, b)$ of the affine lift in $H^2(a, b)$ is the affine lift in
$H^1(a, b)$. -/
theorem inclusionCLM_affineLift (hab : a < b) (α β : ℝ) :
    inclusionCLM 1 a b (affineLift hab 2 α β) = affineLift hab 1 α β :=
  SobolevMultiIndex.ext_of_fn_ae_eq ((fn_affineLift_ae_eq hab 2 α β).trans
    (fn_affineLift_ae_eq hab 1 α β).symm)

open SobolevInterval in
/-- The second derivative of the affine lift in $H^2(a, b)$ is $0$. -/
theorem deriv_affineLift_two (hab : a < b) (α β : ℝ) : deriv (affineLift hab 2 α β) 2 = 0 := by
  have h1 : _root_.deriv (fun x ↦ α + (β - α) * ((x - a) / (b - a)))
      = fun _ ↦ (β - α) * (b - a)⁻¹ := by
    funext y
    have : HasDerivAt (fun x ↦ α + (β - α) * ((x - a) / (b - a))) ((β - α) * (b - a)⁻¹) y := by
      have := (((hasDerivAt_id y).sub_const a).div_const (b - a)).const_mul (β - α) |>.const_add α
      simpa using this
    exact this.deriv
  have h2 : iteratedDeriv 2 (fun x ↦ α + (β - α) * ((x - a) / (b - a))) = fun _ ↦ 0 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, h1]
    funext y
    exact deriv_const y _
  refine Lp.ext ?_
  rw [affineLift, ContDiffMapIcc.deriv_toSobolevInterval]
  refine (ContDiffMapIcc.coeFn_derivLp _ 2).trans ?_
  refine (Lp.coeFn_zero ℝ 2 (volume.restrict (Ioo a b))).mono fun x hx ↦ ?_
  rw [hx, Pi.zero_apply]
  change ContDiffMapIcc.deriv _ 2 (projIcc a b hab.le x) = 0
  rw [ContDiffMapIcc.deriv_ofContDiff, show ((2 : Fin 3) : ℕ) = 2 from rfl, h2]

/-- **The Dirichlet class** of Example 1, Method 2, in §8.4 of [brezis2011functional]: for
$\alpha, \beta \in \mathbb{R}$,
$$K = \{v \in H^1(a, b) : v(a) = \alpha, v(b) = \beta\}.$$
-/
def dirichletSet (a b : ℝ) (α β : ℝ) : Set (SobolevInterval 1 a b) :=
  {v | SobolevInterval.rep v a = α ∧ SobolevInterval.rep v b = β}

/-- $v \in K$ if and only if $v(a) = \alpha$ and $v(b) = \beta$. -/
theorem mem_dirichletSet_iff (α β : ℝ) (v : SobolevInterval 1 a b) :
    v ∈ dirichletSet a b α β ↔ SobolevInterval.rep v a = α ∧ SobolevInterval.rep v b = β :=
  Iff.rfl

/-- For $a < b$, the Dirichlet class $K$ is closed in $H^1(a, b)$.

It is cut out by the two evaluation functionals at $a$ and at $b$, which are continuous. -/
theorem isClosed_dirichletSet (hab : a < b) (α β : ℝ) : IsClosed (dirichletSet a b α β) := by
  have h1 : IsClosed {v : SobolevInterval 1 a b | SobolevInterval.rep v a = α} :=
    isClosed_singleton.preimage (SobolevInterval.evalCLM hab ⟨a, left_mem_Icc.2 hab.le⟩).continuous
  have h2 : IsClosed {v : SobolevInterval 1 a b | SobolevInterval.rep v b = β} :=
    isClosed_singleton.preimage (SobolevInterval.evalCLM hab ⟨b, right_mem_Icc.2 hab.le⟩).continuous
  exact h1.inter h2

open SobolevInterval in
/-- Let $a < b$ and let $u_0$ be the affine lift with the values $\alpha$ at $a$ and $\beta$ at $b$.
Then $v \in K$ if and only if $v - u_0 \in H^1_0(a, b)$. -/
theorem mem_dirichletSet_iff_sub_mem (hab : a < b) (α β : ℝ) (v : SobolevInterval 1 a b) :
    v ∈ dirichletSet a b α β ↔ v - affineLift hab 1 α β ∈ SobolevIntervalZero a b := by
  have h : v - affineLift hab 1 α β ∈ SobolevIntervalZero a b
      ↔ rep (v - affineLift hab 1 α β) a = 0 ∧ rep (v - affineLift hab 1 α β) b = 0 :=
    mem_sobolevIntervalZero_iff hab _
  have ha := rep_sub hab v (affineLift hab 1 α β) (left_mem_Icc.2 hab.le)
  have hb := rep_sub hab v (affineLift hab 1 α β) (right_mem_Icc.2 hab.le)
  simp only [Pi.sub_apply] at ha hb
  rw [h, mem_dirichletSet_iff, ha, hb, rep_affineLift_left, rep_affineLift_right, sub_eq_zero,
    sub_eq_zero]

/-- For $a < b$, the Dirichlet class $K$ is convex. -/
theorem convex_dirichletSet (hab : a < b) (α β : ℝ) : Convex ℝ (dirichletSet a b α β) := by
  intro v hv w hw s t hs ht hst
  rw [mem_dirichletSet_iff_sub_mem hab] at hv hw ⊢
  have : s • v + t • w - affineLift hab 1 α β
      = s • (v - affineLift hab 1 α β) + t • (w - affineLift hab 1 α β) := by
    calc s • v + t • w - affineLift hab 1 α β
        = s • v + t • w - (s + t) • affineLift hab 1 α β := by rw [hst, one_smul]
      _ = _ := by rw [add_smul, smul_sub, smul_sub]; abel
  rw [this]
  exact (SobolevIntervalZero a b).add_mem ((SobolevIntervalZero a b).smul_mem s hv)
    ((SobolevIntervalZero a b).smul_mem t hw)

/-- For $a < b$, the affine lift lies in the Dirichlet class $K$. -/
theorem affineLift_mem_dirichletSet (hab : a < b) (α β : ℝ) :
    affineLift hab 1 α β ∈ dirichletSet a b α β :=
  ⟨rep_affineLift_left hab α β, rep_affineLift_right hab α β⟩

/-- For $a < b$, the Dirichlet class $K$ is nonempty. -/
theorem nonempty_dirichletSet (hab : a < b) (α β : ℝ) : (dirichletSet a b α β).Nonempty :=
  ⟨_, affineLift_mem_dirichletSet hab α β⟩

/-- **The space of the mixed problem** of Example 5 in §8.4 of [brezis2011functional]: the subspace
$$\{v \in H^1(a, b) : v(a) = 0\},$$
which is the kernel of the evaluation at $a$. -/
def mixedSpace (hab : a < b) : Submodule ℝ (SobolevInterval 1 a b) :=
  LinearMap.ker ((SobolevInterval.evalCLM hab ⟨a, left_mem_Icc.2 hab.le⟩ :
    SobolevInterval 1 a b →L[ℝ] ℝ) : SobolevInterval 1 a b →ₗ[ℝ] ℝ)

/-- **The space of the Robin problem** of Example 6 in §8.4 of [brezis2011functional]: the subspace
$$\{v \in H^1(a, b) : v(b) = 0\},$$
which is the kernel of the evaluation at $b$. -/
def robinSpace (hab : a < b) : Submodule ℝ (SobolevInterval 1 a b) :=
  LinearMap.ker ((SobolevInterval.evalCLM hab ⟨b, right_mem_Icc.2 hab.le⟩ :
    SobolevInterval 1 a b →L[ℝ] ℝ) : SobolevInterval 1 a b →ₗ[ℝ] ℝ)

/-- **The space of the periodic problem** of Example 7 in §8.4 of [brezis2011functional]: the
subspace
$$\{v \in H^1(a, b) : v(a) = v(b)\}.$$
-/
def periodicSpace (hab : a < b) : Submodule ℝ (SobolevInterval 1 a b) :=
  LinearMap.ker ((SobolevInterval.evalCLM hab ⟨a, left_mem_Icc.2 hab.le⟩
    - SobolevInterval.evalCLM hab ⟨b, right_mem_Icc.2 hab.le⟩ :
    SobolevInterval 1 a b →L[ℝ] ℝ) : SobolevInterval 1 a b →ₗ[ℝ] ℝ)

/-- $v$ is in the space of the mixed problem if and only if $v(a) = 0$. -/
theorem mem_mixedSpace_iff (hab : a < b) (v : SobolevInterval 1 a b) :
    v ∈ mixedSpace hab ↔ SobolevInterval.rep v a = 0 :=
  LinearMap.mem_ker (f := ((SobolevInterval.evalCLM hab ⟨a, left_mem_Icc.2 hab.le⟩ :
    SobolevInterval 1 a b →L[ℝ] ℝ) : SobolevInterval 1 a b →ₗ[ℝ] ℝ))

/-- $v$ is in the space of the Robin problem if and only if $v(b) = 0$. -/
theorem mem_robinSpace_iff (hab : a < b) (v : SobolevInterval 1 a b) :
    v ∈ robinSpace hab ↔ SobolevInterval.rep v b = 0 :=
  LinearMap.mem_ker (f := ((SobolevInterval.evalCLM hab ⟨b, right_mem_Icc.2 hab.le⟩ :
    SobolevInterval 1 a b →L[ℝ] ℝ) : SobolevInterval 1 a b →ₗ[ℝ] ℝ))

/-- $v$ is in the space of the periodic problem if and only if $v(a) = v(b)$. -/
theorem mem_periodicSpace_iff (hab : a < b) (v : SobolevInterval 1 a b) :
    v ∈ periodicSpace hab ↔ SobolevInterval.rep v a = SobolevInterval.rep v b := by
  rw [periodicSpace, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, sub_apply, sub_eq_zero]
  rfl

/-- The space of the mixed problem is closed in $H^1(a, b)$. -/
theorem isClosed_mixedSpace (hab : a < b) :
    IsClosed (mixedSpace hab : Set (SobolevInterval 1 a b)) :=
  ContinuousLinearMap.isClosed_ker _

/-- The space of the Robin problem is closed in $H^1(a, b)$. -/
theorem isClosed_robinSpace (hab : a < b) :
    IsClosed (robinSpace hab : Set (SobolevInterval 1 a b)) :=
  ContinuousLinearMap.isClosed_ker _

/-- The space of the periodic problem is closed in $H^1(a, b)$. -/
theorem isClosed_periodicSpace (hab : a < b) :
    IsClosed (periodicSpace hab : Set (SobolevInterval 1 a b)) :=
  ContinuousLinearMap.isClosed_ker _

/-- $H^1_0(a, b)$ is contained in the space of the mixed problem. -/
theorem sobolevIntervalZero_le_mixedSpace (hab : a < b) :
    SobolevIntervalZero a b ≤ mixedSpace hab := fun _ hv ↦
  (mem_mixedSpace_iff hab _).2 (SobolevIntervalZero.rep_left_eq_zero hab hv)

/-- $H^1_0(a, b)$ is contained in the space of the Robin problem. -/
theorem sobolevIntervalZero_le_robinSpace (hab : a < b) :
    SobolevIntervalZero a b ≤ robinSpace hab := fun _ hv ↦
  (mem_robinSpace_iff hab _).2 (SobolevIntervalZero.rep_right_eq_zero hab hv)

/-- $H^1_0(a, b)$ is contained in the space of the periodic problem. -/
theorem sobolevIntervalZero_le_periodicSpace (hab : a < b) :
    SobolevIntervalZero a b ≤ periodicSpace hab := fun _ hv ↦
  (mem_periodicSpace_iff hab _).2 (by
    rw [SobolevIntervalZero.rep_left_eq_zero hab hv, SobolevIntervalZero.rep_right_eq_zero hab hv])

/-! ### The natural boundary conditions, case by case -/

open SobolevInterval in
/-- **The Neumann conditions are natural.** Let $a < b$, $f \in L^2(a, b)$,
$w_0, w_1 \in \mathbb{R}$, and let $\Phi \in H^2(a, b)$ satisfy
$$\int_a^b (\Phi' v' + \Phi v) = \int_a^b f v + w_1 v(b) - w_0 v(a)
  \quad \text{for every } v \in H^1(a, b).$$
Then $-\Phi'' + \Phi = f$ almost everywhere on $(a, b)$, $\Phi'(a) = w_0$ and $\Phi'(b) = w_1$. -/
theorem natural_boundary_neumann (hab : a < b) (f : Lp ℝ 2 (volume.restrict (Ioo a b)))
    {w₀ w₁ : ℝ} (Φ : SobolevInterval 2 a b) (h : ∀ v, modelForm a b (inclusionCLM 1 a b Φ) v
      = load a b f v + w₁ * rep v b - w₀ * rep v a) :
    ((deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] fun x ↦ fn Φ x - f x) ∧
      rep (derivCLM 1 a b Φ) a = w₀ ∧ rep (derivCLM 1 a b Φ) b = w₁ := by
  obtain ⟨heq, hbd⟩ := natural_boundary_eq_of_forall hab f (K := ⊤) le_top Φ fun v _ ↦ h v
  refine ⟨heq, ?_, ?_⟩
  · have := hbd (affineLift hab 1 1 0) trivial
    rw [rep_affineLift_left, rep_affineLift_right, mul_zero, mul_one] at this
    linarith
  · have := hbd (affineLift hab 1 0 1) trivial
    rw [rep_affineLift_left, rep_affineLift_right, mul_zero, mul_one] at this
    linarith

open SobolevInterval in
/-- **The natural condition of the mixed problem.** Let $a < b$, $f \in L^2(a, b)$,
$w_1 \in \mathbb{R}$, and let $\Phi \in H^2(a, b)$ satisfy
$$\int_a^b (\Phi' v' + \Phi v) = \int_a^b f v + w_1 v(b)
  \quad \text{for every } v \in H^1(a, b) \text{ with } v(a) = 0.$$
Then $-\Phi'' + \Phi = f$ almost everywhere on $(a, b)$, and $\Phi'(b) = w_1$.

The other condition of the mixed problem, $\Phi(a) = 0$, is essential: it comes from the
membership of $\Phi$ in the space, which this statement does not assume. -/
theorem natural_boundary_mixed (hab : a < b) (f : Lp ℝ 2 (volume.restrict (Ioo a b)))
    {w₁ : ℝ} (Φ : SobolevInterval 2 a b) (h : ∀ v ∈ mixedSpace hab,
      modelForm a b (inclusionCLM 1 a b Φ) v = load a b f v + w₁ * rep v b) :
    ((deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] fun x ↦ fn Φ x - f x) ∧
      rep (derivCLM 1 a b Φ) b = w₁ := by
  obtain ⟨heq, hbd⟩ := natural_boundary_eq_of_forall hab f (w₀ := 0)
    (sobolevIntervalZero_le_mixedSpace hab) Φ fun v hv ↦ by rw [h v hv]; ring
  refine ⟨heq, ?_⟩
  have := hbd (affineLift hab 1 0 1) ((mem_mixedSpace_iff hab _).2 (rep_affineLift_left hab 0 1))
  rw [rep_affineLift_left, rep_affineLift_right, mul_zero, mul_one] at this
  linarith

open SobolevInterval in
/-- **The natural condition of the Robin problem.** Let $a < b$, $f \in L^2(a, b)$,
$w_0 \in \mathbb{R}$, and let $\Phi \in H^2(a, b)$ satisfy
$$\int_a^b (\Phi' v' + \Phi v) = \int_a^b f v - w_0 v(a)
  \quad \text{for every } v \in H^1(a, b) \text{ with } v(b) = 0.$$
Then $-\Phi'' + \Phi = f$ almost everywhere on $(a, b)$, and $\Phi'(a) = w_0$. -/
theorem natural_boundary_robin (hab : a < b) (f : Lp ℝ 2 (volume.restrict (Ioo a b)))
    {w₀ : ℝ} (Φ : SobolevInterval 2 a b) (h : ∀ v ∈ robinSpace hab,
      modelForm a b (inclusionCLM 1 a b Φ) v = load a b f v - w₀ * rep v a) :
    ((deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] fun x ↦ fn Φ x - f x) ∧
      rep (derivCLM 1 a b Φ) a = w₀ := by
  obtain ⟨heq, hbd⟩ := natural_boundary_eq_of_forall hab f (w₁ := 0)
    (sobolevIntervalZero_le_robinSpace hab) Φ fun v hv ↦ by rw [h v hv]; ring
  refine ⟨heq, ?_⟩
  have := hbd (affineLift hab 1 1 0) ((mem_robinSpace_iff hab _).2 (rep_affineLift_right hab 1 0))
  rw [rep_affineLift_left, rep_affineLift_right, mul_zero, mul_one] at this
  linarith

open SobolevInterval in
/-- **The natural condition of the periodic problem.** Let $a < b$, $f \in L^2(a, b)$, and let
$\Phi \in H^2(a, b)$ satisfy
$$\int_a^b (\Phi' v' + \Phi v) = \int_a^b f v
  \quad \text{for every } v \in H^1(a, b) \text{ with } v(a) = v(b).$$
Then $-\Phi'' + \Phi = f$ almost everywhere on $(a, b)$, and $\Phi'(a) = \Phi'(b)$.

The other condition of the periodic problem, $\Phi(a) = \Phi(b)$, is essential: it comes from
the membership of $\Phi$ in the space, which this statement does not assume. -/
theorem natural_boundary_periodic (hab : a < b) (f : Lp ℝ 2 (volume.restrict (Ioo a b)))
    (Φ : SobolevInterval 2 a b) (h : ∀ v ∈ periodicSpace hab,
      modelForm a b (inclusionCLM 1 a b Φ) v = load a b f v) :
    ((deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] fun x ↦ fn Φ x - f x) ∧
      rep (derivCLM 1 a b Φ) a = rep (derivCLM 1 a b Φ) b := by
  obtain ⟨heq, hbd⟩ := natural_boundary_eq_of_forall hab f (w₀ := 0) (w₁ := 0)
    (sobolevIntervalZero_le_periodicSpace hab) Φ fun v hv ↦ by rw [h v hv]; ring
  refine ⟨heq, ?_⟩
  have := hbd (affineLift hab 1 1 1) ((mem_periodicSpace_iff hab _).2 (by
    rw [rep_affineLift_left, rep_affineLift_right]))
  rw [rep_affineLift_left, rep_affineLift_right, mul_one, mul_one] at this
  linarith

/-! ### Proposition 8.16: the inhomogeneous Dirichlet problem -/

/-- **The inhomogeneous Dirichlet problem by Stampacchia's method.** Let $a < b$, $f \in L^2(a, b)$
and $\alpha, \beta \in \mathbb{R}$, and let $K = \{v \in H^1(a, b) : v(a) = \alpha, v(b) =
\beta\}$. Then there is exactly one $u \in K$ with
$$\int_a^b f (v - u) \le \int_a^b u' (v - u)' + \int_a^b u (v - u)
  \quad \text{for every } v \in K.$$
This is the variational inequality (17) of Proposition 8.16, Method 2, of
[brezis2011functional]. -/
theorem existsUnique_dirichletSet_of_variationalInequality (hab : a < b)
    (f : Lp ℝ 2 (volume.restrict (Ioo a b))) (α β : ℝ) :
    ∃! u, u ∈ dirichletSet a b α β ∧
      ∀ v ∈ dirichletSet a b α β, load a b f (v - u) ≤ modelForm a b u (v - u) := by
  have h := existsUnique_isVariationalInequalitySolution_of_isCoercive one_pos
    (modelForm_isCoerciveWith (a := a) (b := b)) (nonempty_dirichletSet hab α β)
    (isClosed_dirichletSet hab α β) (convex_dirichletSet hab α β)
    (convexOn_const 0 (convex_dirichletSet hab α β)) lowerSemicontinuousOn_const (load a b f)
  refine (existsUnique_congr fun u ↦ ?_).1 h
  simp only [IsVariationalInequalitySolution, SesqForm.inner_rieszRep, SesqForm.inner_toOperator,
    add_zero, sub_zero]

/-- Let $a < b$, $f \in L^2(a, b)$, and let $u$ be in the Dirichlet class $K$ and solve the
variational inequality (17). Then $\int_a^b (u' w' + u w) = \int_a^b f w$ for every
$w \in H^1_0(a, b)$.

The proof tests the inequality with $v = u \pm w$. -/
theorem forall_modelForm_eq_load_of_variationalInequality (hab : a < b)
    (f : Lp ℝ 2 (volume.restrict (Ioo a b))) {α β : ℝ} {u : SobolevInterval 1 a b}
    (hu : u ∈ dirichletSet a b α β)
    (hvi : ∀ v ∈ dirichletSet a b α β, load a b f (v - u) ≤ modelForm a b u (v - u)) :
    ∀ w ∈ SobolevIntervalZero a b, modelForm a b u w = load a b f w := by
  intro w hw
  rw [mem_dirichletSet_iff_sub_mem hab] at hu
  have h1 : u + w ∈ dirichletSet a b α β := by
    rw [mem_dirichletSet_iff_sub_mem hab, add_sub_right_comm]
    exact (SobolevIntervalZero a b).add_mem hu hw
  have h2 : u - w ∈ dirichletSet a b α β := by
    rw [mem_dirichletSet_iff_sub_mem hab, sub_right_comm]
    exact (SobolevIntervalZero a b).sub_mem hu hw
  have e1 := hvi _ h1
  have e2 := hvi _ h2
  rw [add_sub_cancel_left] at e1
  rw [sub_sub_cancel_left, map_neg, map_neg] at e2
  linarith

/-- **The inhomogeneous Dirichlet problem.** Let $a < b$, $f \in L^2(a, b)$ and
$\alpha, \beta \in \mathbb{R}$. Then there is exactly one $\Phi \in H^2(a, b)$ with
$-\Phi'' + \Phi = f$ almost everywhere on $(a, b)$, $\Phi(a) = \alpha$ and $\Phi(b) = \beta$.
This is Proposition 8.16 of [brezis2011functional].

Existence comes from the variational inequality of Method 2 and Step C. For uniqueness, a
solution satisfies the weak equation against $H^1_0(a, b)$ by Green's formula, hence the
variational inequality, which has one solution. -/
theorem existsUnique_dirichlet_inhomogeneous (hab : a < b)
    (f : Lp ℝ 2 (volume.restrict (Ioo a b))) (α β : ℝ) :
    ∃! Φ : SobolevInterval 2 a b,
      ((SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)]
        fun x ↦ SobolevInterval.fn Φ x - f x) ∧
      SobolevInterval.inclusionCLM 1 a b Φ ∈ dirichletSet a b α β := by
  obtain ⟨u, ⟨huK, hvi⟩, huniq⟩ := existsUnique_dirichletSet_of_variationalInequality hab f α β
  have hweak := forall_modelForm_eq_load_of_variationalInequality hab f huK hvi
  obtain ⟨Φ, hΦ, heq⟩ := exists_sobolevInterval_two_of_forall_modelForm f hweak
  refine ⟨Φ, ⟨heq, hΦ ▸ huK⟩, fun Ψ ⟨hΨeq, hΨK⟩ ↦ ?_⟩
  have hΨvi : ∀ v ∈ dirichletSet a b α β,
      load a b f (v - SobolevInterval.inclusionCLM 1 a b Ψ)
        ≤ modelForm a b (SobolevInterval.inclusionCLM 1 a b Ψ)
          (v - SobolevInterval.inclusionCLM 1 a b Ψ) := fun v hv ↦ by
    have hmem : v - SobolevInterval.inclusionCLM 1 a b Ψ ∈ SobolevIntervalZero a b := by
      rw [mem_dirichletSet_iff_sub_mem hab] at hv hΨK
      have := (SobolevIntervalZero a b).sub_mem hv hΨK
      rwa [sub_sub_sub_cancel_right] at this
    exact (modelForm_inclusionCLM_eq_load_of_mem hab f hΨeq hmem).ge
  have := huniq _ ⟨hΨK, hΨvi⟩
  exact eq_of_inclusionCLM_eq_of_deriv_two f hΨeq heq (this.trans hΦ.symm)

/-- **Dirichlet's principle for the inhomogeneous problem.** Let $a < b$, $f \in L^2(a, b)$, and let
$u$ be in the Dirichlet class $K$. Then $u$ minimizes the energy
$$E(v) = \frac{1}{2} \int_a^b (v'^2 + v^2) - \int_a^b f v$$
over $K$ if and only if $u$ solves the variational inequality (17). -/
theorem dirichletSet_isMinOn_energy_iff (hab : a < b) (f : Lp ℝ 2 (volume.restrict (Ioo a b)))
    {α β : ℝ} {u : SobolevInterval 1 a b} (hu : u ∈ dirichletSet a b α β) :
    IsMinOn ((modelForm a b).energy (load a b f)) (dirichletSet a b α β) u ↔
      ∀ v ∈ dirichletSet a b α β, load a b f (v - u) ≤ modelForm a b u (v - u) :=
  SesqForm.isMinOn_energy_iff_forall_le modelForm_isHermitian (load a b f) one_pos
    modelForm_isCoerciveWith (convex_dirichletSet hab α β) hu

/-! ### Propositions 8.17 and 8.18: the Neumann problems -/

/-- **The weak Neumann problem.** For every continuous linear functional $\ell$ on $H^1(a, b)$ there
is exactly one $u \in H^1(a, b)$ with
$$\int_a^b (u' v' + u v) = \ell(v) \quad \text{for every } v \in H^1(a, b).$$
This is the Lax–Milgram step of Proposition 8.17 of [brezis2011functional]. -/
theorem existsUnique_neumann_weak (ℓ : SobolevInterval 1 a b →L[ℝ] ℝ) :
    ∃! u : SobolevInterval 1 a b, ∀ v, modelForm a b u v = ℓ v :=
  SesqForm.laxMilgram (modelForm a b) ℓ one_pos modelForm_isCoerciveWith

/-- **Dirichlet's principle for the Neumann problem.** Let $\ell$ be a continuous linear functional
on $H^1(a, b)$. Then $u \in H^1(a, b)$ minimizes $\frac{1}{2} \int_a^b (v'^2 + v^2) - \ell(v)$
over $H^1(a, b)$ if and only if $\int_a^b (u' v' + u v) = \ell(v)$ for every $v \in H^1(a, b)$. -/
theorem neumann_isMinOn_energy_iff (ℓ : SobolevInterval 1 a b →L[ℝ] ℝ)
    (u : SobolevInterval 1 a b) :
    IsMinOn ((modelForm a b).energy ℓ) univ u ↔ ∀ v, modelForm a b u v = ℓ v := by
  have := SesqForm.isMinOn_energy_iff ℓ modelForm_isHermitian one_pos modelForm_isCoerciveWith
    (⊤ : Submodule ℝ (SobolevInterval 1 a b)) (u := u) Submodule.mem_top
  rw [Submodule.top_coe] at this
  rw [this]
  exact ⟨fun h v ↦ h v Submodule.mem_top, fun h v _ ↦ h v⟩

open SobolevInterval in
/-- **The homogeneous Neumann problem.** Let $a < b$ and $f \in L^2(a, b)$. Then there is exactly
one $\Phi \in H^2(a, b)$ with $-\Phi'' + \Phi = f$ almost everywhere on $(a, b)$ and
$\Phi'(a) = \Phi'(b) = 0$. This is Proposition 8.17 of [brezis2011functional].

Existence comes from the weak solution on $H^1(a, b)$ (Lax–Milgram), Step C and the natural
boundary conditions. Uniqueness holds because such a $\Phi$ is the weak solution, by Green's
formula. -/
theorem existsUnique_neumann (hab : a < b) (f : Lp ℝ 2 (volume.restrict (Ioo a b))) :
    ∃! Φ : SobolevInterval 2 a b,
      ((deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] fun x ↦ fn Φ x - f x) ∧
      rep (derivCLM 1 a b Φ) a = 0 ∧ rep (derivCLM 1 a b Φ) b = 0 := by
  obtain ⟨u, hu, huniq⟩ := existsUnique_neumann_weak (a := a) (b := b) (load a b f)
  obtain ⟨Φ, hΦ, -⟩ := exists_sobolevInterval_two_of_forall_modelForm f fun v _ ↦ hu v
  have hnat := natural_boundary_neumann hab f (w₀ := 0) (w₁ := 0) Φ fun v ↦ by
    rw [hΦ, hu v]; ring
  refine ⟨Φ, hnat, fun Ψ ⟨hΨeq, hΨa, hΨb⟩ ↦ ?_⟩
  have hΨ : ∀ v, modelForm a b (inclusionCLM 1 a b Ψ) v = load a b f v := fun v ↦ by
    rw [modelForm_inclusionCLM_eq_of_deriv_two hab f hΨeq v, hΨa, hΨb]; ring
  exact eq_of_inclusionCLM_eq_of_deriv_two f hΨeq hnat.1 ((huniq _ hΨ).trans hΦ.symm)

/-- **The inhomogeneous Neumann load** of Example 4 in §8.4 of [brezis2011functional]: for $a < b$,
$f \in L^2(a, b)$ and $\alpha, \beta \in \mathbb{R}$, the continuous linear functional
$$v \mapsto \int_a^b f v - \alpha v(a) + \beta v(b)$$
on $H^1(a, b)$. It is continuous by the embedding $H^1(a, b) \hookrightarrow C[a, b]$ (Theorem
8.8 of the source). -/
def neumannLoad (hab : a < b) (f : Lp ℝ 2 (volume.restrict (Ioo a b))) (α β : ℝ) :
    SobolevInterval 1 a b →L[ℝ] ℝ :=
  load a b f - α • SobolevInterval.evalCLM hab ⟨a, left_mem_Icc.2 hab.le⟩
    + β • SobolevInterval.evalCLM hab ⟨b, right_mem_Icc.2 hab.le⟩

/-- The inhomogeneous Neumann load at $v$ is $\int_a^b f v - \alpha v(a) + \beta v(b)$. -/
theorem neumannLoad_apply (hab : a < b) (f : Lp ℝ 2 (volume.restrict (Ioo a b))) (α β : ℝ)
    (v : SobolevInterval 1 a b) :
    neumannLoad hab f α β v
      = load a b f v - α * SobolevInterval.rep v a + β * SobolevInterval.rep v b := by
  simp only [neumannLoad, add_apply, sub_apply, smul_apply, smul_eq_mul,
    SobolevInterval.evalCLM_apply]

open SobolevInterval in
/-- **The inhomogeneous Neumann problem.** Let $a < b$, $f \in L^2(a, b)$ and
$\alpha, \beta \in \mathbb{R}$. Then there is exactly one $\Phi \in H^2(a, b)$ with
$-\Phi'' + \Phi = f$ almost everywhere on $(a, b)$, $\Phi'(a) = \alpha$ and $\Phi'(b) = \beta$.
This is Proposition 8.18 of [brezis2011functional].

The inclusion of $\Phi$ in $H^1(a, b)$ is the weak solution with the load $v \mapsto \int_a^b f
v - \alpha v(a) + \beta v(b)$. -/
theorem existsUnique_neumann_inhomogeneous (hab : a < b)
    (f : Lp ℝ 2 (volume.restrict (Ioo a b))) (α β : ℝ) :
    ∃! Φ : SobolevInterval 2 a b,
      ((deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] fun x ↦ fn Φ x - f x) ∧
      rep (derivCLM 1 a b Φ) a = α ∧ rep (derivCLM 1 a b Φ) b = β := by
  obtain ⟨u, hu, huniq⟩ := existsUnique_neumann_weak (a := a) (b := b) (neumannLoad hab f α β)
  have hu0 : ∀ v ∈ SobolevIntervalZero a b, modelForm a b u v = load a b f v := fun v hv ↦ by
    rw [hu v, neumannLoad_apply, SobolevIntervalZero.rep_left_eq_zero hab hv,
      SobolevIntervalZero.rep_right_eq_zero hab hv]
    ring
  obtain ⟨Φ, hΦ, -⟩ := exists_sobolevInterval_two_of_forall_modelForm f hu0
  have hnat := natural_boundary_neumann hab f (w₀ := α) (w₁ := β) Φ fun v ↦ by
    rw [hΦ, hu v, neumannLoad_apply]; ring
  refine ⟨Φ, hnat, fun Ψ ⟨hΨeq, hΨa, hΨb⟩ ↦ ?_⟩
  have hΨ : ∀ v, modelForm a b (inclusionCLM 1 a b Ψ) v = neumannLoad hab f α β v := fun v ↦ by
    rw [modelForm_inclusionCLM_eq_of_deriv_two hab f hΨeq v, hΨa, hΨb, neumannLoad_apply]; ring
  exact eq_of_inclusionCLM_eq_of_deriv_two f hΨeq hnat.1 ((huniq _ hΨ).trans hΦ.symm)

/-! ### Examples 5–7: the mixed, Robin and periodic problems -/

/-- Let $V$ be a real Hilbert space, let $a$ be a bounded bilinear form on $V$ with
$a(v, v) \ge c \|v\|^2$ for every $v$ and a constant $c > 0$, let $\ell$ be a continuous linear
functional on $V$, and let $K$ be a closed subspace of $V$. Then there is exactly one $u \in K$
with $a(u, v) = \ell(v)$ for every $v \in K$.

This is the Lax–Milgram theorem on $K$. -/
theorem existsUnique_isGalerkinSolution_of_isClosed {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] {a : SesqForm ℝ V} {c : ℝ} (hc : 0 < c)
    (ha : a.IsCoerciveWith c) (ℓ : V →L[ℝ] ℝ) {K : Submodule ℝ V} (hK : IsClosed (K : Set V)) :
    ∃! u, IsGalerkinSolution a ℓ K u :=
  have : CompleteSpace K := hK.completeSpace_coe
  IsGalerkinSolution.existsUnique hc ha

open SobolevInterval in
/-- **The mixed problem.** Let $a < b$ and $f \in L^2(a, b)$. Then there is exactly one
$\Phi \in H^2(a, b)$ with $-\Phi'' + \Phi = f$ almost everywhere on $(a, b)$, $\Phi(a) = 0$ and
$\Phi'(b) = 0$. This is Example 5 in §8.4 of [brezis2011functional].

The proof applies the Lax–Milgram theorem on the closed subspace $\{v : v(a) = 0\}$, then Step
C, and then the natural condition at $b$. -/
theorem existsUnique_mixed (hab : a < b) (f : Lp ℝ 2 (volume.restrict (Ioo a b))) :
    ∃! Φ : SobolevInterval 2 a b,
      ((deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] fun x ↦ fn Φ x - f x) ∧
      rep (inclusionCLM 1 a b Φ) a = 0 ∧ rep (derivCLM 1 a b Φ) b = 0 := by
  obtain ⟨u, ⟨huK, hu⟩, huniq⟩ := existsUnique_isGalerkinSolution_of_isClosed one_pos
    (modelForm_isCoerciveWith (a := a) (b := b)) (load a b f) (isClosed_mixedSpace hab)
  obtain ⟨Φ, hΦ, -⟩ := exists_sobolevInterval_two_of_forall_modelForm f
    fun v hv ↦ hu v (sobolevIntervalZero_le_mixedSpace hab hv)
  have hnat := natural_boundary_mixed hab f (w₁ := 0) Φ fun v hv ↦ by rw [hΦ, hu v hv]; ring
  refine ⟨Φ, ⟨hnat.1, hΦ ▸ (mem_mixedSpace_iff hab u).1 huK, hnat.2⟩, fun Ψ ⟨hΨeq, hΨa, hΨb⟩ ↦ ?_⟩
  have hΨ : IsGalerkinSolution (modelForm a b) (load a b f) (mixedSpace hab)
      (inclusionCLM 1 a b Ψ) := by
    refine ⟨(mem_mixedSpace_iff hab _).2 hΨa, fun v hv ↦ ?_⟩
    rw [modelForm_inclusionCLM_eq_of_deriv_two hab f hΨeq v, hΨb,
      (mem_mixedSpace_iff hab v).1 hv]
    ring
  exact eq_of_inclusionCLM_eq_of_deriv_two f hΨeq hnat.1 ((huniq _ hΨ).trans hΦ.symm)

/-- **The Robin form** of Example 6 in §8.4 of [brezis2011functional]: for $a < b$ and
$k \in \mathbb{R}$, the bilinear form
$$a(u, v) = \int_a^b (u' v' + u v) + k \, u(a) v(a)$$
on $H^1(a, b)$. -/
def robinForm (hab : a < b) (k : ℝ) : SesqForm ℝ (SobolevInterval 1 a b) :=
  modelForm a b + k • (((innerSL ℝ).comp
    (SobolevInterval.evalCLM hab ⟨a, left_mem_Icc.2 hab.le⟩)).flip.comp
    (SobolevInterval.evalCLM hab ⟨a, left_mem_Icc.2 hab.le⟩)).flip

/-- The Robin form at $(u, v)$ is $\int_a^b (u' v' + u v) + k \, u(a) v(a)$. -/
theorem robinForm_apply (hab : a < b) (k : ℝ) (u v : SobolevInterval 1 a b) :
    robinForm hab k u v
      = modelForm a b u v + k * (SobolevInterval.rep u a * SobolevInterval.rep v a) := by
  simp only [robinForm, add_apply, smul_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul, innerSL_apply_apply, RCLike.inner_apply,
    conj_trivial, SobolevInterval.evalCLM_apply]
  ring

/-- The Robin form is Hermitian, that is, symmetric. -/
theorem robinForm_isHermitian (hab : a < b) (k : ℝ) : (robinForm hab k).IsHermitian := fun u v ↦ by
  rw [robinForm_apply, robinForm_apply, modelForm_comm, mul_comm (SobolevInterval.rep u a)]
  rfl

/-- The Robin form is symmetric: $a(u, v) = a(v, u)$ for all $u, v \in H^1(a, b)$. -/
theorem robinForm_comm (hab : a < b) (k : ℝ) (u v : SobolevInterval 1 a b) :
    robinForm hab k u v = robinForm hab k v u :=
  robinForm_isHermitian hab k u v

/-- **The Robin form is coercive for $k \ge 0$**, with constant $1$: $a(v, v) \ge \|v\|_{H^1}^2$ for
every $v \in H^1(a, b)$.

The reason is that $a(v, v) = \|v\|_{H^1}^2 + k \, v(a)^2$. -/
theorem robinForm_isCoerciveWith (hab : a < b) {k : ℝ} (hk : 0 ≤ k) :
    (robinForm hab k).IsCoerciveWith 1 := fun v ↦ by
  rw [RCLike.re_to_real, robinForm_apply, modelForm_apply, real_inner_self_eq_norm_sq, one_mul]
  nlinarith [mul_self_nonneg (SobolevInterval.rep v a)]

open SobolevInterval in
/-- **The Robin problem.** Let $a < b$, $f \in L^2(a, b)$ and $k \ge 0$. Then there is exactly one
$\Phi \in H^2(a, b)$ with $-\Phi'' + \Phi = f$ almost everywhere on $(a, b)$,
$\Phi'(a) = k \, \Phi(a)$ and $\Phi(b) = 0$. This is Example 6 in §8.4 of
[brezis2011functional].

The proof applies the Lax–Milgram theorem for the Robin form on the closed subspace
$\{v : v(b) = 0\}$, then Step C, and then the natural condition at $a$. The boundary term
$k \, u(a) v(a)$ of the form becomes the datum $w_0 = k \, u(a)$. -/
theorem existsUnique_robin (hab : a < b) (f : Lp ℝ 2 (volume.restrict (Ioo a b))) {k : ℝ}
    (hk : 0 ≤ k) :
    ∃! Φ : SobolevInterval 2 a b,
      ((deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] fun x ↦ fn Φ x - f x) ∧
      rep (derivCLM 1 a b Φ) a = k * rep (inclusionCLM 1 a b Φ) a ∧
      rep (inclusionCLM 1 a b Φ) b = 0 := by
  obtain ⟨u, ⟨huK, hu⟩, huniq⟩ := existsUnique_isGalerkinSolution_of_isClosed one_pos
    (robinForm_isCoerciveWith hab hk) (load a b f) (isClosed_robinSpace hab)
  have hu' : ∀ v ∈ robinSpace hab, modelForm a b u v = load a b f v - k * rep u a * rep v a :=
    fun v hv ↦ by rw [← hu v hv, robinForm_apply]; ring
  obtain ⟨Φ, hΦ, -⟩ := exists_sobolevInterval_two_of_forall_modelForm f fun v hv ↦ by
    rw [hu' v (sobolevIntervalZero_le_robinSpace hab hv),
      SobolevIntervalZero.rep_left_eq_zero hab hv]
    ring
  have hnat := natural_boundary_robin hab f (w₀ := k * rep u a) Φ fun v hv ↦ by
    rw [hΦ, hu' v hv]
  refine ⟨Φ, ⟨hnat.1, hΦ ▸ hnat.2, hΦ ▸ (mem_robinSpace_iff hab u).1 huK⟩,
    fun Ψ ⟨hΨeq, hΨa, hΨb⟩ ↦ ?_⟩
  have hΨ : IsGalerkinSolution (robinForm hab k) (load a b f) (robinSpace hab)
      (inclusionCLM 1 a b Ψ) := by
    refine ⟨(mem_robinSpace_iff hab _).2 hΨb, fun v hv ↦ ?_⟩
    rw [robinForm_apply, modelForm_inclusionCLM_eq_of_deriv_two hab f hΨeq v, hΨa,
      (mem_robinSpace_iff hab v).1 hv]
    ring
  exact eq_of_inclusionCLM_eq_of_deriv_two f hΨeq hnat.1 ((huniq _ hΨ).trans hΦ.symm)

open SobolevInterval in
/-- **The periodic problem.** Let $a < b$ and $f \in L^2(a, b)$. Then there is exactly one
$\Phi \in H^2(a, b)$ with $-\Phi'' + \Phi = f$ almost everywhere on $(a, b)$,
$\Phi(a) = \Phi(b)$ and $\Phi'(a) = \Phi'(b)$. This is Example 7 in §8.4 of
[brezis2011functional].

The proof applies the Lax–Milgram theorem on the closed subspace $\{v : v(a) = v(b)\}$, then
Step C, and then the natural condition, which is the periodicity of the derivative. -/
theorem existsUnique_periodic (hab : a < b) (f : Lp ℝ 2 (volume.restrict (Ioo a b))) :
    ∃! Φ : SobolevInterval 2 a b,
      ((deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] fun x ↦ fn Φ x - f x) ∧
      rep (inclusionCLM 1 a b Φ) a = rep (inclusionCLM 1 a b Φ) b ∧
      rep (derivCLM 1 a b Φ) a = rep (derivCLM 1 a b Φ) b := by
  obtain ⟨u, ⟨huK, hu⟩, huniq⟩ := existsUnique_isGalerkinSolution_of_isClosed one_pos
    (modelForm_isCoerciveWith (a := a) (b := b)) (load a b f) (isClosed_periodicSpace hab)
  obtain ⟨Φ, hΦ, -⟩ := exists_sobolevInterval_two_of_forall_modelForm f
    fun v hv ↦ hu v (sobolevIntervalZero_le_periodicSpace hab hv)
  have hnat := natural_boundary_periodic hab f Φ fun v hv ↦ by rw [hΦ, hu v hv]
  refine ⟨Φ, ⟨hnat.1, hΦ ▸ (mem_periodicSpace_iff hab u).1 huK, hnat.2⟩,
    fun Ψ ⟨hΨeq, hΨa, hΨb⟩ ↦ ?_⟩
  have hΨ : IsGalerkinSolution (modelForm a b) (load a b f) (periodicSpace hab)
      (inclusionCLM 1 a b Ψ) := by
    refine ⟨(mem_periodicSpace_iff hab _).2 hΨa, fun v hv ↦ ?_⟩
    rw [modelForm_inclusionCLM_eq_of_deriv_two hab f hΨeq v, hΨb,
      (mem_periodicSpace_iff hab v).1 hv]
    ring
  exact eq_of_inclusionCLM_eq_of_deriv_two f hΨeq hnat.1 ((huniq _ hΨ).trans hΦ.symm)

/-! ### The $C^2$ part for the model problem -/

open SobolevInterval in
/-- **A solution of the model equation with continuous datum is $C^2$.** Let $a < b$, let
$f \in L^2(a, b)$ agree almost everywhere on $(a, b)$ with a function $f$ that is continuous on
$[a, b]$, and let $\Phi \in H^2(a, b)$ satisfy $-\Phi'' + \Phi = f$ almost everywhere on
$(a, b)$. Then there is $v \in C^2[a, b]$ that carries the inclusion of $\Phi$ in $H^1(a, b)$,
with
$$-v''(x) + v(x) = f(x) \quad \text{for every } x \in (a, b).$$
This is the $C^2$ part of Propositions 8.16–8.18 and Examples 5–7 in §8.4 of
[brezis2011functional].

"$v$ carries the inclusion of $\Phi$" means
`EllipticInterval.ofContDiffMapIcc hab v = SobolevInterval.inclusionCLM 1 a b Φ`. -/
theorem exists_contDiffMapIcc_of_deriv_two (hab : a < b) (fL : Lp ℝ 2 (volume.restrict (Ioo a b)))
    {f : ℝ → ℝ} (hfL : fL =ᵐ[volume.restrict (Ioo a b)] f) (hf : ContinuousOn f (Icc a b))
    {Φ : SobolevInterval 2 a b}
    (hΦ : (deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] fun x ↦ fn Φ x - fL x) :
    ∃ v : ContDiffMapIcc hab.le 2, ofContDiffMapIcc hab v = inclusionCLM 1 a b Φ ∧
      ∀ x ∈ Ioo a b, -_root_.deriv v.shift.extend x + v.extend x = f x := by
  obtain ⟨v, hv, hode⟩ := exists_contDiffMapIcc_of_continuous hab (constLinf a b 1) 0
    (constLinf a b 1) fL (α := fun _ ↦ 1) (β := fun _ ↦ 0) (γ := fun _ ↦ 1) (f := f)
    (coeFn_constLinf a b 1) (Lp.coeFn_zero ℝ ⊤ _) (coeFn_constLinf a b 1) hfL contDiffOn_const
    (fun _ _ ↦ one_ne_zero) continuousOn_const continuousOn_const hf
    (fun w hw ↦ modelForm_inclusionCLM_eq_load_of_mem hab fL hΦ hw)
  refine ⟨v, hv, fun x hx ↦ ?_⟩
  have := hode x hx
  simp only [one_mul, zero_mul, add_zero] at this
  exact this

/-! ### Example 8: the problem on $\mathbb{R}$ -/

namespace Line

/-- The Hölder exponents $(2, 2, 1)$ satisfy $\frac{1}{2} + \frac{1}{2} = \frac{1}{1}$, so the
product of two $L^2$ functions is integrable. -/
theorem holderTriple_two_two_one : ENNReal.HolderTriple 2 2 1 :=
  ⟨by rw [inv_one]; exact ENNReal.inv_two_add_inv_two⟩

/-- **The form of Example 8** in §8.4 of [brezis2011functional]: the bilinear form
$$a(u, v) = \int_{\mathbb{R}} u' v' + \int_{\mathbb{R}} u v$$
on $H^1(\mathbb{R})$. It is the inner product of $H^1(\mathbb{R})$, and it is coercive with
constant $1$. -/
def form : SesqForm ℝ (SobolevIntervalLp 1 2 ⊤) := innerSL ℝ

/-- The form of Example 8 is the inner product of $H^1(\mathbb{R})$:
$a(u, v) = \langle u, v \rangle$. -/
theorem form_apply (u v : SobolevIntervalLp 1 2 ⊤) : form u v = ⟪u, v⟫_ℝ := rfl

open SobolevIntervalLp in
/-- The form of Example 8 is the integral $a(u, v) = \int_{\mathbb{R}} (u v + u' v')$. -/
theorem form_apply_integral (u v : SobolevIntervalLp 1 2 ⊤) :
    form u v = ∫ x, (fn u x * fn v x + deriv u 1 x * deriv v 1 x) := by
  rw [form_apply, SobolevIntervalLp.inner_eq_integral]
  exact setIntegral_univ

/-- The form of Example 8 is coercive with constant $1$: $a(v, v) \ge \|v\|_{H^1}^2$. -/
theorem form_isCoerciveWith : form.IsCoerciveWith 1 := SesqForm.innerSL_isCoerciveWith

/-- The form of Example 8 is symmetric. -/
theorem form_isHermitian : form.IsHermitian := SesqForm.innerSL_isHermitian

/-- **The load of Example 8**: for $f \in L^2(\mathbb{R})$, the continuous linear functional
$v \mapsto \int_{\mathbb{R}} f v$ on $H^1(\mathbb{R})$. -/
def load (f : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) :
    SobolevIntervalLp 1 2 ⊤ →L[ℝ] ℝ :=
  (innerSL ℝ f).comp (SobolevIntervalLp.derivL 1 2 ⊤ 0)

open SobolevIntervalLp in
/-- The load of Example 8 is the inner product of $L^2(\mathbb{R})$ with $f$:
$v \mapsto \langle f, v \rangle_{L^2}$. -/
theorem load_apply_inner (f : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (v : SobolevIntervalLp 1 2 ⊤) : load f v = ⟪f, deriv v 0⟫_ℝ := rfl

open SobolevIntervalLp in
/-- The load of Example 8 at $v$ is the integral $\int_{\mathbb{R}} f(x) v(x) \, dx$. -/
theorem load_apply (f : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (v : SobolevIntervalLp 1 2 ⊤) : load f v = ∫ x, f x * fn v x := by
  rw [load_apply_inner, L2.inner_def]
  refine (integral_congr_ae (Eventually.of_forall fun x ↦ ?_)).trans
    (setIntegral_univ (μ := volume) (f := fun x ↦ f x * fn v x))
  simp [RCLike.inner_apply, mul_comm, deriv_zero]

/-- **The weak solution of Example 8**: for $f \in L^2(\mathbb{R})$, the unique
$u \in H^1(\mathbb{R})$ with
$$\langle u, v \rangle_{H^1} = \int_{\mathbb{R}} f v
  \quad \text{for every } v \in H^1(\mathbb{R}).$$

It is given by the Riesz–Fréchet representation theorem, which is the Lax–Milgram theorem for
the inner product. -/
def solution (f : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) : SobolevIntervalLp 1 2 ⊤ :=
  (InnerProductSpace.toDual ℝ (SobolevIntervalLp 1 2 ⊤)).symm (load f)

/-- The weak solution $u$ of Example 8 solves the weak problem: $a(u, v) = \int_{\mathbb{R}} f v$
for every $v \in H^1(\mathbb{R})$. -/
theorem form_solution (f : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (v : SobolevIntervalLp 1 2 ⊤) : form (solution f) v = load f v := by
  change ⟪solution f, v⟫_ℝ = load f v
  exact InnerProductSpace.toDual_symm_apply

/-- The weak problem of Example 8 has exactly one solution: if $u \in H^1(\mathbb{R})$ and
$a(u, v) = \int_{\mathbb{R}} f v$ for every $v \in H^1(\mathbb{R})$, then $u$ is the weak
solution `EllipticInterval.Line.solution f`. -/
theorem eq_solution_of_forall {f : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    {u : SobolevIntervalLp 1 2 ⊤} (hu : ∀ v, form u v = load f v) : u = solution f := by
  rw [solution, LinearIsometryEquiv.eq_symm_apply]
  ext v
  exact hu v

/-! ### Example 8: a classical solution lies in $H^1(\mathbb{R})$ -/

/-- A continuous function $u : \mathbb{R} \to \mathbb{R}$ that tends to $0$ at infinity is bounded:
there is $M$ with $|u(x)| \le M$ for every $x$. -/
theorem exists_forall_abs_le_of_tendsto_cocompact {u : ℝ → ℝ} (hu : Continuous u)
    (h : Tendsto u (cocompact ℝ) (𝓝 0)) : ∃ M, ∀ x, |u x| ≤ M := by
  obtain ⟨K, hK, hKu⟩ := Filter.hasBasis_cocompact.eventually_iff.1
    (Metric.tendsto_nhds.1 h 1 one_pos)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hu.continuousOn
  refine ⟨max C 1, fun x ↦ ?_⟩
  by_cases hx : x ∈ K
  · exact (Real.norm_eq_abs _ ▸ hC x hx).trans (le_max_left _ _)
  · have := hKu hx
    rw [dist_zero_right, Real.norm_eq_abs] at this
    exact this.le.trans (le_max_right _ _)

/-- The pointwise inequality behind the a priori estimate: for all real numbers
$\eta, \eta', u, u', f$,
$$\eta^2 u f - 2 \eta \eta' u u'
  \le \tfrac{1}{2} \eta^2 f^2 + \tfrac{1}{2} \eta^2 (u^2 + u'^2) + 2 \eta'^2 u^2.$$

The proof uses $2 x y \le x^2 + y^2$ twice. -/
theorem amgm_aux (η η' uu uu' ff : ℝ) :
    η ^ 2 * uu * ff - 2 * η * η' * uu * uu'
      ≤ 1 / 2 * (η ^ 2 * ff ^ 2) + 1 / 2 * (η ^ 2 * (uu ^ 2 + uu' ^ 2))
        + 2 * (η' ^ 2 * uu ^ 2) := by
  nlinarith [sq_nonneg (η * uu - η * ff), sq_nonneg (η * uu' + 2 * η' * uu)]

/-- Let $\zeta_n$ be the cut-off `SobolevIntervalLp.cutoffFn n`, which vanishes off
$(-2(n+1), 2(n+1))$. If $|x| > 2(n+1)$, then $\zeta_n'(x) = 0$. -/
theorem deriv_cutoffFn_of_lt_abs {n : ℕ} {x : ℝ} (hx : 2 * ((n : ℝ) + 1) < |x|) :
    _root_.deriv (SobolevIntervalLp.cutoffFn n) x = 0 := by
  have h : SobolevIntervalLp.cutoffFn n =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
    have : {y : ℝ | 2 * ((n : ℝ) + 1) < |y|} ∈ 𝓝 x :=
      (isOpen_lt continuous_const continuous_abs).mem_nhds hx
    filter_upwards [this] with y hy
    exact SobolevIntervalLp.cutoffFn_of_le_abs hy.le
  rw [h.deriv_eq, deriv_const]

open SobolevIntervalLp in
/-- **The a priori estimate for a classical solution of $-u'' + u = f$ on $\mathbb{R}$.** Let
$u \in C^2(\mathbb{R})$ be bounded, $|u| \le M$, let $f \in L^2(\mathbb{R})$, and let
$-u'' + u = f$ at every point. Then there is $K$ with
$$\int_{-n-1}^{n+1} (u^2 + u'^2) \le K \quad \text{for every } n \in \mathbb{N}.$$
This is the cut-off argument of Example 8 in §8.4 of [brezis2011functional].

Multiply the equation by $\zeta_n^2 u$ and integrate by parts once: $\int \zeta_n^2 (u^2 +
u'^2) = \int \zeta_n^2 u f - 2 \int \zeta_n \zeta_n' u u'$. The right side is at most
$\frac{1}{2} \int f^2 + \frac{1}{2} \int \zeta_n^2 (u^2 + u'^2) + 2 \int \zeta_n'^2 u^2$, and
the last term is bounded by $|\zeta_n'| \le C/(n+1)$ and the bound on $u$. The source multiplies
by $\zeta_n u$; the proof here uses $\zeta_n^2$, so that no second derivative of the cut-off is
needed. The hypothesis $u \to 0$ at infinity of the source enters only through the boundedness
of $u$. -/
theorem exists_forall_setIntegral_sq_add_sq_le {u f : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    (hf : MemLp f 2 volume) (hode : ∀ x, -_root_.deriv (_root_.deriv u) x + u x = f x) {M : ℝ}
    (hM : ∀ x, |u x| ≤ M) :
    ∃ K : ℝ, ∀ n : ℕ, ∫ x in Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1),
      (u x ^ 2 + _root_.deriv u x ^ 2) ≤ K := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_deriv_cutoffFn_le
  refine ⟨(∫ x, f x ^ 2) + 16 * C ^ 2 * M ^ 2, fun n ↦ ?_⟩
  set η := cutoffFn n with hηdef
  set R : ℝ := 2 * ((n : ℝ) + 1) with hRdef
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  -- smoothness facts
  have hηc : ContDiff ℝ 1 η := (contDiff_cutoffFn n).of_le (by simp)
  have hηd : Differentiable ℝ η := hηc.differentiable one_ne_zero
  have hηs : HasCompactSupport η := hasCompactSupport_cutoffFn n
  have hη1 : ∀ x, |x| ≤ (n : ℝ) + 1 → η x = 1 := fun x hx ↦ cutoffFn_of_abs_le hx
  have hu1 : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hu' : ContDiff ℝ 1 (_root_.deriv u) := by
    have hu2 : ContDiff ℝ ((1 : ℕ∞ω) + 1) u := by rw [one_add_one_eq_two]; exact hu
    exact ((contDiff_succ_iff_deriv (n := 1)).1 hu2).2.2
  have hu'd : Differentiable ℝ (_root_.deriv u) := hu'.differentiable one_ne_zero
  have hu'c : Continuous (_root_.deriv u) := hu'.continuous
  have huc : Continuous u := hu.continuous
  have hode' : ∀ x, _root_.deriv (_root_.deriv u) x = u x - f x := fun x ↦ by
    have := hode x; linarith
  -- the functions of the integration by parts
  set U : ℝ → ℝ := fun x ↦ η x ^ 2 * u x with hUdef
  set U' : ℝ → ℝ := fun x ↦ 2 * η x * _root_.deriv η x * u x + η x ^ 2 * _root_.deriv u x
    with hU'def
  set V' : ℝ → ℝ := fun x ↦ u x - f x with hV'def
  have hU : ∀ x, HasDerivAt U (U' x) x := fun x ↦ by
    have h1 : HasDerivAt (fun y ↦ η y * η y)
        (_root_.deriv η x * η x + η x * _root_.deriv η x) x :=
      (hηd x).hasDerivAt.mul (hηd x).hasDerivAt
    have h2 := h1.mul (hu1 x).hasDerivAt
    have h3 : HasDerivAt U ((_root_.deriv η x * η x + η x * _root_.deriv η x) * u x
        + η x * η x * _root_.deriv u x) x := by
      refine h2.congr_of_eventuallyEq (Eventually.of_forall fun y ↦ ?_)
      simp only [hUdef, sq, Pi.mul_apply]
    exact h3.congr_deriv (by simp only [hU'def]; ring)
  have hV : ∀ x, HasDerivAt (_root_.deriv u) (V' x) x := fun x ↦ by
    have := (hu'd x).hasDerivAt
    rw [hode' x] at this
    exact this
  -- integrability
  have hcs : ∀ g : ℝ → ℝ, (∀ x, η x = 0 → g x = 0) → HasCompactSupport g := fun g hg ↦
    hηs.mono fun x hx ↦ by
      rw [Function.mem_support] at hx ⊢
      exact fun h ↦ hx (hg x h)
  have hcs' : ∀ g : ℝ → ℝ, (∀ x, _root_.deriv η x = 0 → g x = 0) → HasCompactSupport g :=
    fun g hg ↦ hηs.deriv.mono fun x hx ↦ by
      rw [Function.mem_support] at hx ⊢
      exact fun h ↦ hx (hg x h)
  have hUL2 : MemLp U 2 volume :=
    Continuous.memLp_of_hasCompactSupport (by fun_prop) (hcs _ fun x hx ↦ by simp [hUdef, hx])
  have i1 : Integrable (fun x ↦ η x ^ 2 * u x ^ 2) volume :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) (hcs _ fun x hx ↦ by simp [hx])
  have i2 : Integrable (fun x ↦ η x ^ 2 * _root_.deriv u x ^ 2) volume :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) (hcs _ fun x hx ↦ by simp [hx])
  have i3 : Integrable (fun x ↦ η x ^ 2 * u x * f x) volume := by
    have := hUL2.mul (r := 1) (hpqr := holderTriple_two_two_one) hf
    exact memLp_one_iff_integrable.1 this
  have i4 : Integrable (fun x ↦ η x * _root_.deriv η x * u x * _root_.deriv u x) volume :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) (hcs _ fun x hx ↦ by simp [hx])
  have i5 : Integrable (fun x ↦ η x ^ 2 * f x ^ 2) volume := by
    refine hf.integrable_sq.bdd_mul (c := 1) (hηc.continuous.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_one₀ (cutoffFn_nonneg n x) (cutoffFn_le_one n x)
  have i6 : Integrable (fun x ↦ _root_.deriv η x ^ 2 * u x ^ 2) volume :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) (hcs' _ fun x hx ↦ by simp [hx])
  -- integration by parts on the line
  have ibp := integral_mul_deriv_eq_deriv_mul_of_integrable (u := U) (v := _root_.deriv u)
    (u' := U') (v' := V') (fun x _ ↦ hU x) (fun x _ ↦ hV x) ?_ ?_ ?_
  rotate_left
  · have : Integrable (fun x ↦ η x ^ 2 * u x * u x - η x ^ 2 * u x * f x) volume :=
      (by simpa only [sq, mul_assoc] using i1 : Integrable (fun x ↦ η x ^ 2 * u x * u x) volume).sub
        i3
    refine this.congr (Eventually.of_forall fun x ↦ ?_)
    simp only [Pi.mul_apply, hUdef, hV'def]; ring
  · have : Integrable (fun x ↦ 2 * (η x * _root_.deriv η x * u x * _root_.deriv u x)
        + η x ^ 2 * _root_.deriv u x ^ 2) volume := (i4.const_mul 2).add i2
    refine this.congr (Eventually.of_forall fun x ↦ ?_)
    simp only [Pi.mul_apply, hU'def]; ring
  · have : Integrable (fun x ↦ η x ^ 2 * u x * _root_.deriv u x) volume :=
      Continuous.integrable_of_hasCompactSupport (by fun_prop) (hcs _ fun x hx ↦ by simp [hx])
    exact this.congr (Eventually.of_forall fun x ↦ by simp only [Pi.mul_apply, hUdef])
  -- the identity `∫ η² (u² + u'²) = ∫ η² u f − 2 ∫ η η' u u'`
  have e1 : ∫ x, U x * V' x = (∫ x, η x ^ 2 * u x ^ 2) - ∫ x, η x ^ 2 * u x * f x := by
    rw [← integral_sub i1 i3]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only [hUdef, hV'def]; ring)
  have e2 : ∫ x, U' x * _root_.deriv u x
      = 2 * (∫ x, η x * _root_.deriv η x * u x * _root_.deriv u x)
        + ∫ x, η x ^ 2 * _root_.deriv u x ^ 2 := by
    rw [← integral_const_mul, ← integral_add (i4.const_mul 2) i2]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only [hU'def]; ring)
  rw [e1, e2] at ibp
  -- the AM–GM bound
  have hamgm0 : ∫ x, (η x ^ 2 * u x * f x - 2 * (η x * _root_.deriv η x * u x * _root_.deriv u x))
      ≤ ∫ x, (1 / 2 * (η x ^ 2 * f x ^ 2)
        + 1 / 2 * (η x ^ 2 * u x ^ 2 + η x ^ 2 * _root_.deriv u x ^ 2)
        + 2 * (_root_.deriv η x ^ 2 * u x ^ 2)) := by
    refine integral_mono (i3.sub (i4.const_mul 2))
      (((i5.const_mul _).add ((i1.add i2).const_mul _)).add (i6.const_mul _)) fun x ↦ ?_
    simp only
    have := amgm_aux (η x) (_root_.deriv η x) (u x) (_root_.deriv u x) (f x)
    linarith
  have hL : ∫ x, (η x ^ 2 * u x * f x - 2 * (η x * _root_.deriv η x * u x * _root_.deriv u x))
      = (∫ x, η x ^ 2 * u x * f x)
        - 2 * ∫ x, η x * _root_.deriv η x * u x * _root_.deriv u x := by
    rw [integral_sub i3 (i4.const_mul 2), integral_const_mul]
  have hR : ∫ x, (1 / 2 * (η x ^ 2 * f x ^ 2)
        + 1 / 2 * (η x ^ 2 * u x ^ 2 + η x ^ 2 * _root_.deriv u x ^ 2)
        + 2 * (_root_.deriv η x ^ 2 * u x ^ 2))
      = 1 / 2 * (∫ x, η x ^ 2 * f x ^ 2)
        + 1 / 2 * ((∫ x, η x ^ 2 * u x ^ 2) + ∫ x, η x ^ 2 * _root_.deriv u x ^ 2)
        + 2 * ∫ x, _root_.deriv η x ^ 2 * u x ^ 2 := by
    have j1 : Integrable (fun x ↦ 1 / 2 * (η x ^ 2 * f x ^ 2)) volume := i5.const_mul _
    have j12 : Integrable (fun x ↦ η x ^ 2 * u x ^ 2 + η x ^ 2 * _root_.deriv u x ^ 2) volume :=
      i1.add i2
    have j2 : Integrable
        (fun x ↦ 1 / 2 * (η x ^ 2 * u x ^ 2 + η x ^ 2 * _root_.deriv u x ^ 2)) volume :=
      j12.const_mul _
    have j3 : Integrable (fun x ↦ 2 * (_root_.deriv η x ^ 2 * u x ^ 2)) volume := i6.const_mul _
    have j4 : Integrable (fun x ↦ 1 / 2 * (η x ^ 2 * f x ^ 2)
        + 1 / 2 * (η x ^ 2 * u x ^ 2 + η x ^ 2 * _root_.deriv u x ^ 2)) volume := j1.add j2
    rw [integral_add j4 j3, integral_add j1 j2, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_add i1 i2]
  have hamgm := hamgm0
  rw [hL, hR] at hamgm
  -- the bound on `∫ η'² u²`
  have hE : ∫ x, _root_.deriv η x ^ 2 * u x ^ 2 ≤ 4 * C ^ 2 * M ^ 2 := by
    have hsub : ∫ x, _root_.deriv η x ^ 2 * u x ^ 2
        = ∫ x in Icc (-R) R, _root_.deriv η x ^ 2 * u x ^ 2 := by
      refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ ?_).symm
      have hx' : R < |x| := by
        rw [mem_Icc, not_and_or, not_le, not_le] at hx
        rcases hx with hx | hx
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      rw [deriv_cutoffFn_of_lt_abs hx']
      ring
    rw [hsub]
    calc ∫ x in Icc (-R) R, _root_.deriv η x ^ 2 * u x ^ 2
        ≤ ∫ _ in Icc (-R) R, (C / ((n : ℝ) + 1)) ^ 2 * M ^ 2 := by
          refine setIntegral_mono_on i6.integrableOn (integrableOn_const measure_Icc_lt_top.ne)
            measurableSet_Icc fun x _ ↦ ?_
          have h1 : _root_.deriv η x ^ 2 ≤ (C / ((n : ℝ) + 1)) ^ 2 := by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hC n x) 2
          have h2 : u x ^ 2 ≤ M ^ 2 := by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hM x) 2
          exact mul_le_mul h1 h2 (sq_nonneg _) (sq_nonneg _)
      _ = 2 * R * ((C / ((n : ℝ) + 1)) ^ 2 * M ^ 2) := by
          rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
          ring
      _ = 4 * C ^ 2 * M ^ 2 / ((n : ℝ) + 1) := by
          rw [hRdef]; field_simp; ring
      _ ≤ 4 * C ^ 2 * M ^ 2 := by
          rw [div_le_iff₀ hn1]
          nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) (sq_nonneg C)) (sq_nonneg M)]
  -- the bound on `∫ η² f²`
  have hF : ∫ x, η x ^ 2 * f x ^ 2 ≤ ∫ x, f x ^ 2 := by
    refine integral_mono i5 hf.integrable_sq fun x ↦ ?_
    simp only
    have : η x ^ 2 ≤ 1 := pow_le_one₀ (cutoffFn_nonneg n x) (cutoffFn_le_one n x)
    nlinarith [sq_nonneg (f x)]
  -- the bound on the truncated integral
  have hAB : (∫ x, η x ^ 2 * u x ^ 2) + ∫ x, η x ^ 2 * _root_.deriv u x ^ 2
      ≤ (∫ x, f x ^ 2) + 16 * C ^ 2 * M ^ 2 := by linarith
  calc ∫ x in Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1), (u x ^ 2 + _root_.deriv u x ^ 2)
      = ∫ x in Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1),
          (η x ^ 2 * u x ^ 2 + η x ^ 2 * _root_.deriv u x ^ 2) := by
        refine setIntegral_congr_fun measurableSet_Icc fun x hx ↦ ?_
        have : |x| ≤ (n : ℝ) + 1 := abs_le.2 ⟨hx.1, hx.2⟩
        simp only [hη1 x this, one_pow, one_mul]
    _ ≤ ∫ x, (η x ^ 2 * u x ^ 2 + η x ^ 2 * _root_.deriv u x ^ 2) :=
        setIntegral_le_integral (i1.add i2) (Eventually.of_forall fun x ↦ by
          simp only [Pi.zero_apply]; positivity)
    _ = (∫ x, η x ^ 2 * u x ^ 2) + ∫ x, η x ^ 2 * _root_.deriv u x ^ 2 := integral_add i1 i2
    _ ≤ _ := hAB

/-- A continuous function $g : \mathbb{R} \to \mathbb{R}$ with $\int_{-n-1}^{n+1} g^2 \le K$ for
every $n \in \mathbb{N}$ lies in $L^2(\mathbb{R})$.

The proof uses monotone convergence. -/
theorem memLp_two_of_forall_setIntegral_sq_le {g : ℝ → ℝ} (hg : Continuous g) {K : ℝ}
    (h : ∀ n : ℕ, ∫ x in Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1), g x ^ 2 ≤ K) :
    MemLp g 2 volume := by
  rw [memLp_two_iff_integrable_sq hg.aestronglyMeasurable]
  refine ⟨(hg.pow 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  set F : ℕ → ℝ → ℝ≥0∞ := fun n ↦ (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)).indicator
    fun x ↦ ‖g x ^ 2‖ₑ with hF
  have hFm : ∀ n, Measurable (F n) := fun n ↦
    ((hg.pow 2).measurable.enorm).indicator measurableSet_Icc
  have hFmono : Monotone F := fun m n hmn ↦ by
    have hmn' : (m : ℝ) ≤ n := Nat.cast_le.2 hmn
    exact indicator_le_indicator_of_subset
      (Icc_subset_Icc (by linarith) (by linarith)) (fun _ ↦ zero_le)
  have hFsup : ∀ x, ⨆ n, F n x = ‖g x ^ 2‖ₑ := fun x ↦ by
    refine le_antisymm (iSup_le fun n ↦ indicator_le_self _ _ x) ?_
    refine le_iSup_of_le ⌈|x|⌉₊ ?_
    rw [hF]
    simp only
    rw [indicator_of_mem]
    exact abs_le.1 ((Nat.le_ceil |x|).trans (by linarith))
  have key : ∫⁻ x, ‖g x ^ 2‖ₑ = ⨆ n, ∫⁻ x, F n x := by
    rw [← lintegral_iSup hFm hFmono]
    exact lintegral_congr fun x ↦ (hFsup x).symm
  rw [key]
  refine (iSup_le fun n ↦ ?_).trans_lt ENNReal.ofReal_lt_top (b := ENNReal.ofReal K)
  rw [hF]
  simp only
  rw [lintegral_indicator measurableSet_Icc]
  have hint : IntegrableOn (fun x ↦ g x ^ 2) (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) :=
    (hg.pow 2).continuousOn.integrableOn_Icc
  have e : ∫⁻ x in Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1), ‖g x ^ 2‖ₑ
      = ENNReal.ofReal (∫ x in Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1), g x ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x ↦ sq_nonneg _)]
    exact lintegral_congr fun x ↦ Real.enorm_of_nonneg (sq_nonneg _)
  rw [e]
  exact ENNReal.ofReal_le_ofReal (h n)

/-- **A classical solution of $-u'' + u = f$ on $\mathbb{R}$ that tends to $0$ at infinity is square
integrable.** Let $u \in C^2(\mathbb{R})$ satisfy $-u'' + u = f$ at every point, with
$f \in L^2(\mathbb{R})$, and let $u(x) \to 0$ as $|x| \to \infty$. Then $u$ and $u'$ are in
$L^2(\mathbb{R})$. This is part of Example 8 in §8.4 of [brezis2011functional]. -/
theorem memLp_of_classical {u f : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (hf : MemLp f 2 volume)
    (hode : ∀ x, -_root_.deriv (_root_.deriv u) x + u x = f x)
    (hlim : Tendsto u (cocompact ℝ) (𝓝 0)) :
    MemLp u 2 volume ∧ MemLp (_root_.deriv u) 2 volume := by
  obtain ⟨M, hM⟩ := exists_forall_abs_le_of_tendsto_cocompact hu.continuous hlim
  obtain ⟨K, hK⟩ := exists_forall_setIntegral_sq_add_sq_le hu hf hode hM
  have hu'c : Continuous (_root_.deriv u) := hu.continuous_deriv (by norm_num)
  have hi : ∀ n : ℕ, IntegrableOn (fun x ↦ u x ^ 2) (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) :=
    fun n ↦ (hu.continuous.pow 2).continuousOn.integrableOn_Icc
  have hi' : ∀ n : ℕ,
      IntegrableOn (fun x ↦ _root_.deriv u x ^ 2) (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) :=
    fun n ↦ (hu'c.pow 2).continuousOn.integrableOn_Icc
  constructor
  · refine memLp_two_of_forall_setIntegral_sq_le hu.continuous (K := K) fun n ↦ ?_
    have := hK n
    rw [integral_add (hi n) (hi' n)] at this
    have h0 : 0 ≤ ∫ x in Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1), _root_.deriv u x ^ 2 :=
      integral_nonneg fun x ↦ sq_nonneg _
    linarith
  · refine memLp_two_of_forall_setIntegral_sq_le hu'c (K := K) fun n ↦ ?_
    have := hK n
    rw [integral_add (hi n) (hi' n)] at this
    have h0 : 0 ≤ ∫ x in Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1), u x ^ 2 :=
      integral_nonneg fun x ↦ sq_nonneg _
    linarith

/-- **A classical solution of Example 8 lies in $H^1(\mathbb{R})$.** Let $u \in C^2(\mathbb{R})$
satisfy $-u'' + u = f$ at every point, with $f \in L^2(\mathbb{R})$, and let $u(x) \to 0$ as
$|x| \to \infty$. Then $u \in H^1(\mathbb{R})$. This is the first step of Example 8 in §8.4 of
[brezis2011functional]. -/
theorem memSobolevIntervalLp_of_classical {u f : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    (hf : MemLp f 2 volume) (hode : ∀ x, -_root_.deriv (_root_.deriv u) x + u x = f x)
    (hlim : Tendsto u (cocompact ℝ) (𝓝 0)) : MemSobolevIntervalLp u 1 2 ⊤ := by
  obtain ⟨h1, h2⟩ := memLp_of_classical hu hf hode hlim
  exact (memSobolevIntervalLp_of_contDiffOn (hu.of_le (by norm_num)).contDiffOn
    (SobolevIntervalLp.memLp_restrict_top_iff.2 h1)
    (SobolevIntervalLp.memLp_restrict_top_iff.2 h2)).1

/-! ### Example 8: integration by parts on the line, and the weak equation -/

open SobolevIntervalLp in
/-- **Integration by parts on $\mathbb{R}$ for $H^1(\mathbb{R})$.** For $U, v \in H^1(\mathbb{R})$,
with continuous representatives $\tilde U, \tilde v$,
$$\int_{\mathbb{R}} (U' \tilde v + \tilde U v') = 0.$$

The boundary terms of Corollary 8.10 of [brezis2011functional] vanish at infinity by Corollary
8.9 of the source. -/
theorem integral_deriv_mul_rep_add_rep_mul_deriv_eq_zero (U v : SobolevIntervalLp 1 2 ⊤) :
    ∫ x, (deriv U 1 x * rep v x + rep U x * deriv v 1 x) = 0 := by
  have hI := Opens.ordConnected_top
  have hp : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hcl : ∀ x : ℝ, x ∈ closure ((⊤ : Opens ℝ) : Set ℝ) := Opens.mem_closure_top
  -- integrability of the integrand on the line
  have hint : Integrable (fun x ↦ deriv U 1 x * rep v x + rep U x * deriv v 1 x) volume := by
    have h1 : MemLp (fun x ↦ deriv U 1 x * rep v x) 1 volume := by
      have := (memLp_restrict_top_iff.1 (Lp.memLp (deriv U 1))).mul (r := 1)
        (hpqr := holderTriple_two_two_one) (memLp_restrict_top_iff.1 (memLp_rep hI v))
      exact this
    have h2 : MemLp (fun x ↦ rep U x * deriv v 1 x) 1 volume := by
      have := (memLp_restrict_top_iff.1 (memLp_rep hI U)).mul (r := 1)
        (hpqr := holderTriple_two_two_one) (memLp_restrict_top_iff.1 (Lp.memLp (deriv v 1)))
      exact this
    exact memLp_one_iff_integrable.1 (h1.add h2)
  -- the truncated identities and their limits
  have hn : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hn' : Tendsto (fun n : ℕ ↦ -(n : ℝ)) atTop atBot := tendsto_neg_atTop_atBot.comp hn
  have hlim := intervalIntegral_tendsto_integral hint hn' hn
  have hcoc : cocompact ℝ ⊓ 𝓟 ((⊤ : Opens ℝ) : Set ℝ) = cocompact ℝ := by
    rw [Opens.coe_top, principal_univ, inf_top_eq]
  have hU0 : Tendsto (rep U) (cocompact ℝ) (𝓝 0) := hcoc ▸ tendsto_rep_cocompact hI hp U
  have hv0 : Tendsto (rep v) (cocompact ℝ) (𝓝 0) := hcoc ▸ tendsto_rep_cocompact hI hp v
  have hat : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop (cocompact ℝ) := by
    rw [cocompact_eq_atBot_atTop]; exact hn.mono_right le_sup_right
  have hat' : Tendsto (fun n : ℕ ↦ -(n : ℝ)) atTop (cocompact ℝ) := by
    rw [cocompact_eq_atBot_atTop]; exact hn'.mono_right le_sup_left
  have hlim' : Tendsto (fun n : ℕ ↦ ∫ x in -(n : ℝ)..(n : ℝ),
      (deriv U 1 x * rep v x + rep U x * deriv v 1 x)) atTop (𝓝 0) := by
    have e : ∀ n : ℕ, ∫ x in -(n : ℝ)..(n : ℝ), (deriv U 1 x * rep v x + rep U x * deriv v 1 x)
        = rep U n * rep v n - rep U (-n) * rep v (-n) := fun n ↦
      integral_deriv_mul_add_mul_deriv hI U v (hcl _) (hcl _)
    simp_rw [e]
    have := ((hU0.comp hat).mul (hv0.comp hat)).sub ((hU0.comp hat').mul (hv0.comp hat'))
    simpa using this
  exact tendsto_nhds_unique hlim hlim'

open SobolevIntervalLp in
/-- **A classical solution of Example 8 is the weak solution.** Let $u \in C^2(\mathbb{R})$ satisfy
$-u'' + u = f$ at every point, let $f \in L^2(\mathbb{R})$, and let $u(x) \to 0$ as
$|x| \to \infty$. Then the weak solution $U$ of `EllipticInterval.Line.solution f` has the
continuous representative $u$, and $U = u$ almost everywhere. This is part of Example 8 in §8.4
of [brezis2011functional].

The source uses a density argument. The proof here uses integration by parts on $\mathbb{R}$ for
$u' \in H^1(\mathbb{R})$,
`EllipticInterval.Line.integral_deriv_mul_rep_add_rep_mul_deriv_eq_zero`. -/
theorem isWeakSolution_of_classical {u f : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    (fL : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hfL : fL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] f)
    (hode : ∀ x, -_root_.deriv (_root_.deriv u) x + u x = f x)
    (hlim : Tendsto u (cocompact ℝ) (𝓝 0)) :
    ∃ U : SobolevIntervalLp 1 2 ⊤, U = solution fL ∧ (∀ x, rep U x = u x) ∧
      fn U =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] u := by
  have hI := Opens.ordConnected_top
  have hfL' : fL =ᵐ[volume] f := eventuallyEq_restrict_top_iff.1 hfL
  have hf : MemLp f 2 volume := (memLp_restrict_top_iff.1 (Lp.memLp fL)).ae_eq hfL'
  obtain ⟨h1, h2⟩ := memLp_of_classical hu hf hode hlim
  have hode' : ∀ x, _root_.deriv (_root_.deriv u) x = u x - f x := fun x ↦ by
    have := hode x; linarith
  have hu' : ContDiff ℝ 1 (_root_.deriv u) := by
    have hu2 : ContDiff ℝ ((1 : ℕ∞ω) + 1) u := by rw [one_add_one_eq_two]; exact hu
    exact ((contDiff_succ_iff_deriv (n := 1)).1 hu2).2.2
  have h3 : MemLp (_root_.deriv (_root_.deriv u)) 2 volume := by
    have : (fun x ↦ u x - f x) = _root_.deriv (_root_.deriv u) := funext fun x ↦ (hode' x).symm
    exact this ▸ h1.sub hf
  -- the elements `U` and `U₁` of `H¹(ℝ)` carried by `u` and `u'`
  set U : SobolevIntervalLp 1 2 ⊤ := ofContDiffOn (hu.of_le (by norm_num)).contDiffOn
    (memLp_restrict_top_iff.2 h1) (memLp_restrict_top_iff.2 h2) with hUdef
  set U₁ : SobolevIntervalLp 1 2 ⊤ := ofContDiffOn hu'.contDiffOn
    (memLp_restrict_top_iff.2 h2) (memLp_restrict_top_iff.2 h3) with hU₁def
  have hUfn : fn U =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] u := fn_ofContDiffOn_ae_eq _ _ _
  have hUd : ⇑(deriv U 1) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] _root_.deriv u :=
    coeFn_deriv_ofContDiffOn_one _ _ _
  have hU₁d : ⇑(deriv U₁ 1) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      _root_.deriv (_root_.deriv u) := coeFn_deriv_ofContDiffOn_one _ _ _
  have hUrep : ∀ x, rep U x = u x := fun x ↦
    rep_ofContDiffOn hI _ _ _ hu.continuous.continuousOn (Opens.mem_closure_top x)
  have hU₁rep : ∀ x, rep U₁ x = _root_.deriv u x := fun x ↦
    rep_ofContDiffOn hI _ _ _ hu'.continuous.continuousOn (Opens.mem_closure_top x)
  refine ⟨U, eq_solution_of_forall fun v ↦ ?_, hUrep, hUfn⟩
  -- the weak equation
  have hibp := integral_deriv_mul_rep_add_rep_mul_deriv_eq_zero U₁ v
  have hvrep := fn_ae_eq_rep hI v
  rw [form_apply_integral, load_apply]
  -- integrability of the pieces, over the line
  have iuv : Integrable (fun x ↦ u x * rep v x) volume :=
    memLp_one_iff_integrable.1 (h1.mul (r := 1) (hpqr := holderTriple_two_two_one)
      (memLp_restrict_top_iff.1 (memLp_rep hI v)))
  have iu'v' : Integrable (fun x ↦ _root_.deriv u x * deriv v 1 x) volume :=
    memLp_one_iff_integrable.1 (h2.mul (r := 1) (hpqr := holderTriple_two_two_one)
      (memLp_restrict_top_iff.1 (Lp.memLp (deriv v 1))))
  have ifv : Integrable (fun x ↦ f x * rep v x) volume :=
    memLp_one_iff_integrable.1 (hf.mul (r := 1) (hpqr := holderTriple_two_two_one)
      (memLp_restrict_top_iff.1 (memLp_rep hI v)))
  -- `∫ (u − f) ṽ + u' v' = 0`
  have e0 : ∫ x, ((u x - f x) * rep v x + _root_.deriv u x * deriv v 1 x) = 0 := by
    rw [← hibp]
    refine integral_congr_ae ?_
    filter_upwards [eventuallyEq_restrict_top_iff.1 hU₁d] with x hx
    rw [hx, hode' x, hU₁rep x]
  have iufv : Integrable (fun x ↦ (u x - f x) * rep v x) volume :=
    (iuv.sub ifv).congr (Eventually.of_forall fun x ↦ by simp only [Pi.sub_apply]; ring)
  have e0' : ∫ x, (u x - f x) * rep v x = (∫ x, u x * rep v x) - ∫ x, f x * rep v x := by
    rw [← integral_sub iuv ifv]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only; ring)
  rw [integral_add iufv iu'v', e0'] at e0
  have e1 : ∫ x, (fn U x * fn v x + deriv U 1 x * deriv v 1 x)
      = (∫ x, u x * rep v x) + ∫ x, _root_.deriv u x * deriv v 1 x := by
    rw [← integral_add iuv iu'v']
    refine integral_congr_ae ?_
    filter_upwards [eventuallyEq_restrict_top_iff.1 hUfn, eventuallyEq_restrict_top_iff.1 hUd,
      eventuallyEq_restrict_top_iff.1 hvrep] with x hx1 hx2 hx3
    rw [hx1, hx2, hx3]
  have e2 : ∫ x, fL x * fn v x = ∫ x, f x * rep v x := by
    refine integral_congr_ae ?_
    filter_upwards [hfL', eventuallyEq_restrict_top_iff.1 hvrep] with x hx1 hx2
    rw [hx1, hx2]
  rw [e1, e2]
  linarith

end Line

/-! ### Example 8: regularity of the weak solution, and the classical solution -/

namespace Line

open SobolevIntervalLp in
/-- **The weak solution of Example 8 has $u'' = u - f$ weakly.** For $f \in L^2(\mathbb{R})$, the
derivative $u'$ of the weak solution $u$ has the weak derivative $u - f$ on $\mathbb{R}$.

The proof tests the weak equation against the test functions on $\mathbb{R}$. -/
theorem hasWeakDerivOn_deriv_solution (f : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) :
    HasWeakDerivOn (deriv (solution f) 1) (fun x ↦ fn (solution f) x - f x) ⊤ := by
  set u := solution f with hudef
  have hW : MemLp (fun x ↦ fn u x - f x) 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) :=
    (Lp.memLp (deriv u 0)).sub (Lp.memLp f)
  refine hasWeakDerivOn_iff.2 ⟨(Lp.memLp (deriv u 1)).locallyIntegrableOn (Ω := ⊤) one_le_two,
    hW.locallyIntegrableOn (Ω := ⊤) one_le_two, fun φ ↦ ?_⟩
  set v := TestFunction.toSobolevIntervalLp 2 φ with hvdef
  have hφ := TestFunction.fn_toSobolevIntervalLp_ae_eq (p := 2) φ
  have hφ' := TestFunction.coeFn_deriv_toSobolevIntervalLp_one (p := 2) φ
  have key := form_solution f v
  rw [form_apply, inner_eq_integral, load_apply_inner, L2.inner_def] at key
  -- integrability of the pieces
  have i1 : Integrable (fun x ↦ fn u x * φ x) (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) :=
    memLp_one_iff_integrable.1
      ((Lp.memLp (deriv u 0)).mul (r := 1) (hpqr := holderTriple_two_two_one) (φ.memLp' 2))
  have i2 : Integrable (fun x ↦ deriv u 1 x * _root_.deriv φ x)
      (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) :=
    memLp_one_iff_integrable.1
      ((Lp.memLp (deriv u 1)).mul (r := 1) (hpqr := holderTriple_two_two_one) (φ.memLp_deriv 2))
  have i3 : Integrable (fun x ↦ f x * φ x) (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) :=
    memLp_one_iff_integrable.1
      ((Lp.memLp f).mul (r := 1) (hpqr := holderTriple_two_two_one) (φ.memLp' 2))
  have e1 : ∫ x in ((⊤ : Opens ℝ) : Set ℝ), (fn u x * fn v x + deriv u 1 x * deriv v 1 x)
      = (∫ x in ((⊤ : Opens ℝ) : Set ℝ), fn u x * φ x)
        + ∫ x in ((⊤ : Opens ℝ) : Set ℝ), deriv u 1 x * _root_.deriv φ x := by
    rw [← integral_add i1 i2]
    refine integral_congr_ae ?_
    filter_upwards [hφ, hφ'] with x h1 h2
    rw [h1, h2]
  have e2 : ∫ x in ((⊤ : Opens ℝ) : Set ℝ), ⟪f x, deriv v 0 x⟫_ℝ
      = ∫ x in ((⊤ : Opens ℝ) : Set ℝ), f x * φ x := by
    refine integral_congr_ae ?_
    filter_upwards [hφ] with x h1
    rw [deriv_zero, h1, RCLike.inner_apply, conj_trivial, mul_comm]
  rw [e1, e2] at key
  have e3 : ∫ x in ((⊤ : Opens ℝ) : Set ℝ), _root_.deriv φ x * deriv u 1 x
      = ∫ x in ((⊤ : Opens ℝ) : Set ℝ), deriv u 1 x * _root_.deriv φ x :=
    integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
  have e4 : ∫ x in ((⊤ : Opens ℝ) : Set ℝ), φ x * (fn u x - f x)
      = (∫ x in ((⊤ : Opens ℝ) : Set ℝ), fn u x * φ x)
        - ∫ x in ((⊤ : Opens ℝ) : Set ℝ), f x * φ x := by
    rw [← integral_sub i1 i3]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only; ring)
  rw [e3, e4]
  linarith

open SobolevIntervalLp in
/-- **The weak solution of Example 8 lies in $H^2(\mathbb{R})$**, for every $f \in L^2(\mathbb{R})$.
In Example 8 of [brezis2011functional], §8.4: "one easily verifies that the weak solution $u$
belongs to $H^2(\mathbb{R})$". -/
theorem memSobolevIntervalLp_two_solution (f : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) :
    MemSobolevIntervalLp (fn (solution f)) 2 2 ⊤ :=
  memSobolevIntervalLp_succ_iff.2 ⟨Lp.memLp _, deriv (solution f) 1, hasWeakDerivOn_fn _,
    memSobolevIntervalLp_one_iff.2 ⟨Lp.memLp _, _, hasWeakDerivOn_deriv_solution f,
      (Lp.memLp (deriv (solution f) 0)).sub (Lp.memLp f)⟩⟩

open SobolevIntervalLp in
/-- **The weak solution of Example 8 tends to $0$ at infinity**: its continuous representative
$\tilde u$ satisfies $\tilde u(x) \to 0$ as $|x| \to \infty$. This is Corollary 8.9 of
[brezis2011functional]. -/
theorem tendsto_rep_solution_cocompact (f : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) :
    Tendsto (rep (solution f)) (cocompact ℝ) (𝓝 0) := by
  have := tendsto_rep_cocompact Opens.ordConnected_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (solution f)
  rwa [Opens.coe_top, principal_univ, inf_top_eq] at this

open SobolevIntervalLp in
/-- **The weak solution of Example 8 is $C^2$ when $f$ is continuous.** Let $f \in L^2(\mathbb{R})$
agree almost everywhere with a continuous function $f$. Then the continuous representative
$\tilde u$ of the weak solution is in $C^2(\mathbb{R})$, and $-\tilde u'' + \tilde u = f$ at
every point.

The weak second derivative $u'' = u - f$ agrees almost everywhere with a continuous function, so
$u' \in C^1(\mathbb{R})$ by Remark 6 of [brezis2011functional], and then
$u \in C^2(\mathbb{R})$. -/
theorem contDiff_rep_solution (fL : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) {f : ℝ → ℝ}
    (hfL : fL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] f) (hf : Continuous f) :
    ContDiff ℝ 2 (rep (solution fL)) ∧
      ∀ x, -_root_.deriv (_root_.deriv (rep (solution fL))) x + rep (solution fL) x = f x := by
  set u := solution fL with hudef
  have hI := Opens.ordConnected_top
  have hcl : closure ((⊤ : Opens ℝ) : Set ℝ) = univ := by rw [Opens.coe_top, closure_univ]
  have hw := hasWeakDerivOn_deriv_solution fL
  -- `u'` as an element of `H¹(ℝ)`
  set U₁ : SobolevIntervalLp 1 2 ⊤ := mk ![deriv u 1, deriv u 0 - fL] fun j ↦ by
    fin_cases j
    · exact HasWeakIteratedLineDerivOn.of_length_eq_zero rfl _
        ((Lp.memLp _).locallyIntegrableOn (Ω := ⊤) one_le_two)
    · exact hw.congr_ae EventuallyEq.rfl (Lp.coeFn_sub _ _).symm
    with hU₁def
  have hU₁0 : deriv U₁ 0 = deriv u 1 := rfl
  have hU₁1 : deriv U₁ 1 = deriv u 0 - fL := rfl
  set g : ℝ → ℝ := fun x ↦ rep u x - f x with hgdef
  have hgc : Continuous g := by
    have := continuousOn_rep hI u
    rw [hcl, continuousOn_univ] at this
    exact this.sub hf
  have hgae : ⇑(deriv U₁ 1) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] g := by
    rw [hU₁1]
    filter_upwards [Lp.coeFn_sub (deriv u 0) fL, fn_ae_eq_rep hI u, hfL] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h3, hgdef]
    exact congrArg (· - f x) h2
  have h1 := contDiffOn_rep_of_continuousOn_deriv hI U₁ hgc.continuousOn hgae
  have h0 := contDiffOn_rep_of_continuousOn_deriv hI u (continuousOn_rep hI U₁) (by
    rw [← hU₁0]; exact fn_ae_eq_rep hI U₁)
  rw [hcl] at h1 h0
  have hd0 : ∀ x, HasDerivAt (rep u) (rep U₁ x) x := fun x ↦
    hasDerivWithinAt_univ.1 (h0.2 x (mem_univ x))
  have hd1 : ∀ x, HasDerivAt (rep U₁) (g x) x := fun x ↦
    hasDerivWithinAt_univ.1 (h1.2 x (mem_univ x))
  have hderiv0 : _root_.deriv (rep u) = rep U₁ := funext fun x ↦ (hd0 x).deriv
  have hderiv1 : _root_.deriv (rep U₁) = g := funext fun x ↦ (hd1 x).deriv
  refine ⟨?_, fun x ↦ ?_⟩
  · rw [← one_add_one_eq_two, contDiff_succ_iff_deriv]
    refine ⟨fun x ↦ (hd0 x).differentiableAt, fun h ↦ absurd h (by simp), ?_⟩
    rw [hderiv0, contDiff_one_iff_deriv, hderiv1]
    exact ⟨fun x ↦ (hd1 x).differentiableAt, hgc⟩
  · rw [hderiv0, hderiv1, hgdef]
    ring

/-- **Example 8 in §8.4 of [brezis2011functional], conclusion.** Let $f \in L^2(\mathbb{R})$ agree
almost everywhere with a continuous function $f$. Then there is exactly one
$w \in C^2(\mathbb{R})$ with
$$-w'' + w = f \text{ on } \mathbb{R}, \qquad w(x) \to 0 \text{ as } |x| \to \infty.$$

By `EllipticInterval.Line.eq_rep_solution_of_classical`, $w$ is the continuous representative of
the weak solution `EllipticInterval.Line.solution f`. By
`EllipticInterval.Line.memSobolevIntervalLp_two_solution`, the weak solution lies in
$H^2(\mathbb{R})$. -/
theorem exists_classical_solution (fL : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    {f : ℝ → ℝ} (hfL : fL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] f) (hf : Continuous f) :
    ∃! w : ℝ → ℝ, ContDiff ℝ 2 w ∧ (∀ x, -_root_.deriv (_root_.deriv w) x + w x = f x) ∧
      Tendsto w (cocompact ℝ) (𝓝 0) := by
  obtain ⟨h1, h2⟩ := contDiff_rep_solution fL hfL hf
  refine ⟨SobolevIntervalLp.rep (solution fL), ⟨h1, h2, tendsto_rep_solution_cocompact fL⟩,
    fun w ⟨hw1, hw2, hw3⟩ ↦ ?_⟩
  obtain ⟨U, hU, hUrep, -⟩ := isWeakSolution_of_classical hw1 fL hfL hw2 hw3
  funext x
  rw [← hUrep x, hU]

/-- Let $f \in L^2(\mathbb{R})$ agree almost everywhere with a function $f$, and let
$w \in C^2(\mathbb{R})$ satisfy $-w'' + w = f$ at every point and $w(x) \to 0$ as
$|x| \to \infty$. Then $w$ is the continuous representative of the weak solution
`EllipticInterval.Line.solution f`. -/
theorem eq_rep_solution_of_classical (fL : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    {f w : ℝ → ℝ} (hfL : fL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] f) (hw : ContDiff ℝ 2 w)
    (hode : ∀ x, -_root_.deriv (_root_.deriv w) x + w x = f x)
    (hlim : Tendsto w (cocompact ℝ) (𝓝 0)) : w = SobolevIntervalLp.rep (solution fL) := by
  obtain ⟨U, hU, hUrep, -⟩ := isWeakSolution_of_classical hw fL hfL hode hlim
  funext x
  rw [← hUrep x, hU]

end Line

/-! ### Example 8: translations, and the non-compactness of the solution operator -/

namespace Line

open SobolevIntervalLp

/-- The whole line $\mathbb{R}$ is invariant under the translation by every $h \in \mathbb{R}$. -/
theorem isTranslationInvariant_top (h : ℝ) :
    IsTranslationInvariant ((⊤ : Opens ℝ) : Set ℝ) h := fun _ ↦ Iff.rfl

/-- **The translation by $h$ on $L^2(\mathbb{R})$**, $\tau_h f = f(\cdot + h)$, as a linear
isometry.

It is `MeasureTheory.Lp.translate` on the whole line. -/
abbrev translateLp (h : ℝ) : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) →ₗᵢ[ℝ]
    Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) :=
  Lp.translate ℝ 2 (isTranslationInvariant_top h)

/-- **The translation by $h$ on $H^1(\mathbb{R})$**, $\tau_h u = u(\cdot + h)$, as a linear
isometry.

It is `SobolevMultiIndex.translateL` on the whole line. -/
abbrev translate (h : ℝ) : SobolevIntervalLp 1 2 ⊤ →ₗᵢ[ℝ] SobolevIntervalLp 1 2 ⊤ :=
  SobolevMultiIndex.translateL ℝ (Module.Basis.singleton Unit ℝ) 1 2 volume
    (isTranslationInvariant_top h)

/-- For $f \in L^2(\mathbb{R})$, $\tau_h f = f(\cdot + h)$ almost everywhere. -/
theorem coeFn_translateLp (h : ℝ) (f : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) :
    ⇑(translateLp h f) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] fun x ↦ f (x + h) :=
  Lp.coeFn_translate _ f

/-- For $u \in H^1(\mathbb{R})$ and $j = 0, 1$, the $j$-th weak derivative of $\tau_h u$ is the
translate $\tau_h (u^{(j)})$. -/
theorem deriv_translate (h : ℝ) (u : SobolevIntervalLp 1 2 ⊤) (j : Fin 2) :
    deriv (translate h u) j = translateLp h (deriv u j) :=
  rfl

/-- $\tau_h \tau_{-h} f = f$ for every $f \in L^2(\mathbb{R})$. -/
theorem translateLp_translateLp_neg (h : ℝ)
    (f : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) :
    translateLp h (translateLp (-h) f) = f := by
  have := Lp.translate_neg_translate (isTranslationInvariant_top (-h)) f
  simpa using this

/-- $\tau_h \tau_{-h} u = u$ for every $u \in H^1(\mathbb{R})$. -/
theorem translate_translate_neg (h : ℝ) (u : SobolevIntervalLp 1 2 ⊤) :
    translate h (translate (-h) u) = u :=
  SobolevIntervalLp.ext fun j ↦ by
    rw [deriv_translate, deriv_translate, translateLp_translateLp_neg]

/-- **The translations are adjoint to each other on $L^2(\mathbb{R})$**: $\langle \tau_h f, g
\rangle = \langle f, \tau_{-h} g \rangle$ for all $f, g \in L^2(\mathbb{R})$. -/
theorem inner_translateLp_left (h : ℝ)
    (f g : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) :
    ⟪translateLp h f, g⟫_ℝ = ⟪f, translateLp (-h) g⟫_ℝ :=
  Lp.inner_translate (isTranslationInvariant_top h) f g

/-- **The translations are adjoint to each other on $H^1(\mathbb{R})$**: $\langle \tau_h u, v
\rangle = \langle u, \tau_{-h} v \rangle$ for all $u, v \in H^1(\mathbb{R})$. -/
theorem inner_translate_left (h : ℝ) (u v : SobolevIntervalLp 1 2 ⊤) :
    ⟪translate h u, v⟫_ℝ = ⟪u, translate (-h) v⟫_ℝ := by
  conv_lhs => rw [← translate_translate_neg h v]
  exact (translate h).inner_map_map u (translate (-h) v)

/-- The load of a translate: $\int_{\mathbb{R}} (\tau_h f) v = \int_{\mathbb{R}} f \, (\tau_{-h} v)$
for $f \in L^2(\mathbb{R})$ and $v \in H^1(\mathbb{R})$. -/
theorem load_translateLp (h : ℝ) (f : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (v : SobolevIntervalLp 1 2 ⊤) : load (translateLp h f) v = load f (translate (-h) v) := by
  rw [load_apply_inner, load_apply_inner, inner_translateLp_left, deriv_translate]

/-- **The solution operator of $-u'' + u = f$ on $\mathbb{R}$ commutes with the translations**: the
weak solution for the datum $\tau_h f$ is $\tau_h$ of the weak solution for $f$. This is used in
Remark 30 of Chapter 8 of [brezis2011functional].

The proof uses the uniqueness of the weak solution and the translation invariance of the inner
product of $H^1(\mathbb{R})$. -/
theorem solution_translateLp (h : ℝ) (f : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) :
    solution (translateLp h f) = translate h (solution f) :=
  (eq_solution_of_forall fun v ↦ by
    rw [form_apply, inner_translate_left, ← form_apply, form_solution, load_translateLp]).symm

/-- **The solution operator on $\mathbb{R}$ is injective**: the weak solution for
$f \in L^2(\mathbb{R})$ is $0$ if and only if $f = 0$.

If the solution is $0$, then $\int f \varphi = 0$ for every test function $\varphi$, so $f = 0$
almost everywhere (`ae_eq_zero_of_integral_contDiff_smul_eq_zero`). -/
theorem solution_eq_zero_iff (f : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) :
    solution f = 0 ↔ f = 0 := by
  refine ⟨fun h0 ↦ ?_, fun h0 ↦ ?_⟩
  · have hload : ∀ v, load f v = 0 := fun v ↦ by rw [← form_solution, h0, map_zero, zero_apply]
    have hz : ∀ᵐ x ∂(volume.restrict ((⊤ : Opens ℝ) : Set ℝ)), f x = 0 := by
      refine ae_eq_zero_of_integral_contDiff_smul_eq_zero
        ((Lp.memLp f).locallyIntegrable one_le_two) fun g hg hgc ↦ ?_
      have := hload (TestFunction.toSobolevIntervalLp 2 ⟨g, hg, hgc, subset_univ _⟩)
      rw [load_apply_inner, L2.inner_def] at this
      rw [← this]
      refine integral_congr_ae ?_
      filter_upwards [TestFunction.fn_toSobolevIntervalLp_ae_eq (p := 2)
        ⟨g, hg, hgc, subset_univ _⟩] with x hx
      rw [deriv_zero, hx]
      simp [RCLike.inner_apply]
    exact Lp.ext (Filter.EventuallyEq.trans (hz : ⇑f =ᵐ[_] 0) (Lp.coeFn_zero ℝ 2 _).symm)
  · rw [h0]
    exact (eq_solution_of_forall fun v ↦ by
      rw [map_zero, zero_apply, load_apply_inner, inner_zero_left]).symm

/-- **The pairing of a compactly supported $\psi$ with a translate $\tau_h g$ is controlled by the
tail of $g$.** Let $\psi \in L^2(\mathbb{R})$ with $\psi(x) = 0$ for $|x| \ge R$, and let
$g \in L^2(\mathbb{R})$ and $h \in \mathbb{R}$. Then
$$|\langle \psi, \tau_h g \rangle|
  \le \|\psi\| \, \|g\|_{L^2(\mathbb{R} \setminus [-(h - R - 1), \, h - R - 1])}.$$

The proof uses $\langle \psi, \tau_h g \rangle = \langle g, \tau_{-h} \psi \rangle$, and
$\tau_{-h} \psi$ vanishes where $|x| \le h - R - 1$. -/
theorem abs_inner_translateLp_le {ψ : ℝ → ℝ} {R : ℝ} (hR : ∀ x, R ≤ |x| → ψ x = 0)
    (hψL : MemLp ψ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (g : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) (h : ℝ) :
    |⟪hψL.toLp ψ, translateLp h g⟫_ℝ| ≤ ‖hψL.toLp ψ‖ * (eLpNorm g 2
      ((volume.restrict ((⊤ : Opens ℝ) : Set ℝ)).restrict (Icc (-(h - R - 1)) (h - R - 1))ᶜ)).toReal
      := by
  obtain ⟨S, hSdef⟩ : ∃ S : Set ℝ, S = (Icc (-(h - R - 1)) (h - R - 1))ᶜ := ⟨_, rfl⟩
  have hS : MeasurableSet S := by rw [hSdef]; exact measurableSet_Icc.compl
  rw [← hSdef]
  -- `τ_{-h} ψ` vanishes off `S`
  have hτ0 : ∀ᵐ x ∂(volume.restrict ((⊤ : Opens ℝ) : Set ℝ)), x ∉ S →
      translateLp (-h) (hψL.toLp ψ) x = 0 := by
    filter_upwards [coeFn_translateLp (-h) (hψL.toLp ψ),
      (isTranslationInvariant_top (-h)).measurePreserving.quasiMeasurePreserving.ae_eq_comp
        hψL.coeFn_toLp] with x hx1 hx2 hxS
    rw [hx1]
    simp only [Function.comp_apply] at hx2
    rw [hx2]
    refine hR _ ?_
    rw [hSdef, mem_compl_iff, not_not, mem_Icc] at hxS
    linarith [neg_le_abs (x + -h)]
  -- `⟪g, τ_{-h} ψ⟫ = ⟪1_S g, τ_{-h} ψ⟫`
  have hgS : MemLp (S.indicator g) 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) :=
    (Lp.memLp g).indicator hS.nullMeasurableSet
  have e : ⟪g, translateLp (-h) (hψL.toLp ψ)⟫_ℝ
      = ⟪hgS.toLp _, translateLp (-h) (hψL.toLp ψ)⟫_ℝ := by
    rw [L2.inner_def, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hτ0, hgS.coeFn_toLp] with x hx1 hx2
    rw [hx2]
    by_cases hxS : x ∈ S
    · rw [indicator_of_mem hxS]
    · rw [hx1 hxS, inner_zero_right, inner_zero_right]
  rw [real_inner_comm, inner_translateLp_left, e]
  calc |⟪hgS.toLp _, translateLp (-h) (hψL.toLp ψ)⟫_ℝ|
      ≤ ‖hgS.toLp _‖ * ‖translateLp (-h) (hψL.toLp ψ)‖ := abs_real_inner_le_norm _ _
    _ = _ := by
      rw [LinearIsometry.norm_map, Lp.norm_toLp,
        eLpNorm_indicator_eq_eLpNorm_restrict hS.nullMeasurableSet, mul_comm]

/-- Let $\psi \in L^2(\mathbb{R})$ have compact support, let $g \in L^2(\mathbb{R})$, and let
$r_k \to \infty$. Then $\langle \psi, \tau_{r_k} g \rangle \to 0$ as $k \to \infty$. -/
theorem tendsto_inner_translateLp_atTop {ψ : ℝ → ℝ} (hψc : HasCompactSupport ψ)
    (hψL : MemLp ψ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (g : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) {r : ℕ → ℝ}
    (hr : Tendsto r atTop atTop) :
    Tendsto (fun k ↦ ⟪hψL.toLp ψ, translateLp (r k) g⟫_ℝ) atTop (𝓝 0) := by
  obtain ⟨R, -, hR⟩ := hψc.exists_pos_le_norm
  simp only [Real.norm_eq_abs] at hR
  have htail := (tendsto_eLpNorm_restrict_compl_Icc_atTop
    (μ := volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) (p := 2) (by simp) (Lp.memLp g)).comp
    (tendsto_atTop_add_const_right atTop (-R - 1) hr)
  have htail' := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp htail).const_mul
    ‖hψL.toLp ψ‖
  simp only [Function.comp_def, ENNReal.toReal_zero, mul_zero] at htail'
  refine squeeze_zero_norm (fun k ↦ ?_) htail'
  rw [Real.norm_eq_abs]
  have := abs_inner_translateLp_le hR hψL g (r k)
  simpa [sub_eq_add_neg, add_assoc] using this

/-- **The translates of a nonzero function of $L^2(\mathbb{R})$ have no limit.** Let
$g \in L^2(\mathbb{R})$, $g \neq 0$, let $\varphi : \mathbb{N} \to \mathbb{N}$ be strictly
increasing, and let $a \in L^2(\mathbb{R})$. Then $\tau_{\varphi(k)} g$ does not converge to $a$
as $k \to \infty$. This is the argument of Remark 10(c) and Remark 30 of Chapter 8 of
[brezis2011functional].

If $\tau_{\varphi(k)} g \to a$, then $\|a\| = \|g\|$, because the translations are isometries.
But $\langle \psi, a \rangle = \lim_k \langle \psi, \tau_{\varphi(k)} g \rangle = 0$ for every
smooth compactly supported $\psi$, so $a = 0$ (`ae_eq_zero_of_integral_contDiff_smul_eq_zero`). -/
theorem not_tendsto_translateLp {g : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hg : g ≠ 0) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (a : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) :
    ¬ Tendsto (fun k ↦ translateLp (φ k : ℝ) g) atTop (𝓝 a) := by
  intro hlim
  -- `‖a‖ = ‖g‖`
  have hnorm : ‖a‖ = ‖g‖ := by
    have h1 : Tendsto (fun k ↦ ‖translateLp (φ k : ℝ) g‖) atTop (𝓝 ‖a‖) := hlim.norm
    simp only [LinearIsometry.norm_map] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  -- `⟪ψ, a⟫ = 0` for every smooth compactly supported `ψ`
  have hdecay : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∫ x, ψ x • a x ∂(volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) = 0 := by
    intro ψ hψ hψc
    have hψL : MemLp ψ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) :=
      (hψ.continuous.memLp_of_hasCompactSupport hψc).restrict _
    have hpair : ⟪hψL.toLp ψ, a⟫_ℝ = ∫ x, ψ x • a x ∂(volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) := by
      rw [L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hψL.coeFn_toLp] with x hx
      rw [hx]
      simp [RCLike.inner_apply, mul_comm]
    have h1 : Tendsto (fun k ↦ ⟪hψL.toLp ψ, translateLp (φ k : ℝ) g⟫_ℝ) atTop
        (𝓝 ⟪hψL.toLp ψ, a⟫_ℝ) :=
      ((continuous_const.inner continuous_id).tendsto a).comp hlim
    have h2 := tendsto_inner_translateLp_atTop hψc hψL g
      (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop)
    rw [← hpair]
    exact tendsto_nhds_unique h1 h2
  -- hence `a = 0`
  have ha : a = 0 := by
    have hz := ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((Lp.memLp a).locallyIntegrable one_le_two) hdecay
    exact Lp.ext (Filter.EventuallyEq.trans (hz : ⇑a =ᵐ[_] 0) (Lp.coeFn_zero ℝ 2 _).symm)
  rw [ha, norm_zero] at hnorm
  exact hg (norm_eq_zero.1 hnorm.symm)

end Line

end EllipticInterval
