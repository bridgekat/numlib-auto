/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.ODE.Cauchy
import Numlib.Analysis.ODE.HilleYosida
import NumlibSurface.Brezis.Chapter07.Section01

/-!
# Brezis, Section 7.2: The evolution problem $du/dt + Au = 0$ on $[0, +\infty)$

This module formalizes Section 7.2 of [brezis2011functional]. Let $A$ be a maximal monotone operator
on a real Hilbert space $H$. Problem (6) of the source is
$$\frac{du}{dt} + Au = 0 \quad \text{on } [0, +\infty), \qquad u(0) = u_0,$$
for $u \in C^1([0, +\infty); H) \cap C([0, +\infty); D(A))$. The Hille–Yosida theorem (Theorem 7.4)
says that for every $u_0 \in D(A)$ problem (6) has a unique solution, with $|u(t)| \le |u_0|$ and
$|du/dt(t)| = |Au(t)| \le |Au_0|$. The section first recalls the Cauchy–Lipschitz–Picard theorem for
a Lipschitz vector field on a Banach space (Theorem 7.3), and proves two lemmas: the norms $|w(t)|$
and $|dw/dt(t)|$ of a solution of the approximate problem $dw/dt + A_\lambda w = 0$ are
nonincreasing (Lemma 7.1), and $D(A^2)$ is dense in $D(A)$ for the graph norm (Lemma 7.2). Remarks
4–6 describe the convergence of the approximate solutions, the contraction semigroup $S_A(t)$, and
the reduction of $du/dt + Au + \lambda u = 0$ to problem (6).

Theorem 7.3 specializes the backbone module `Numlib.Analysis.ODE.Cauchy`. The other results
specialize `Numlib.Analysis.ODE.HilleYosida`, with the operators of
`Numlib.Analysis.InnerProductSpace.MaximalMonotone`.

## Main definitions

* Problem (6), `Brezis.Chapter07.IsSolution`: $u$ is a solution of problem (6) in the class $C^1([0,
  +\infty); H) \cap C([0, +\infty); D(A))$.

## Main results

* Theorem 7.3, `Brezis.Chapter07.theorem_7_3` (Cauchy, Lipschitz, Picard): for a Lipschitz map $F$
  on a Banach space, the problem $du/dt = F(u)$ on $[0, +\infty)$, $u(0) = u_0$, has a unique $C^1$
  solution.
* Theorem 7.4, `Brezis.Chapter07.theorem_7_4` (Hille–Yosida): for $u_0 \in D(A)$ problem (6) has a
  unique solution, with $|u(t)| \le |u_0|$ and $|du/dt(t)| = |Au(t)| \le |Au_0|$.
* Lemma 7.1, `Brezis.Chapter07.lemma_7_1`: for a solution $w$ of $dw/dt + A_\lambda w = 0$, the
  functions $|w(t)|$ and $|dw/dt(t)| = |A_\lambda w(t)|$ are nonincreasing.
* Lemma 7.2, `Brezis.Chapter07.lemma_7_2`: $D(A^2)$ is dense in $D(A)$ for the graph norm.
* Remark 4(a), `Brezis.Chapter07.remark_7_4_a`: for $u_0 \in D(A)$, the approximate solutions
  $u_\lambda(t) = e^{-tA_\lambda} u_0$ converge to the solution of problem (6), uniformly on bounded
  intervals.
* Remark 4(b), `Brezis.Chapter07.remark_7_4_b`: for every $u_0 \in H$, $u_\lambda(t)$ converges for
  every $t \ge 0$.
* Remark 5, `Brezis.Chapter07.remark_7_5`: the operators $S_A(t)$ form a continuous semigroup of
  contractions.
* Remark 6, `Brezis.Chapter07.remark_7_6`: the problem $du/dt + Au + \lambda u = 0$ reduces to
  problem (6) through $v(t) = e^{\lambda t} u(t)$.

## Proof outline

The backbone solves the approximate problem (7) of the source,
$du_\lambda/dt + A_\lambda u_\lambda = 0$, $u_\lambda(0) = u_0$, in closed form:
$u_\lambda(t) = e^{-tA_\lambda} u_0$, the backbone's `LinearPMap.expYosida`. It defines the
semigroup $S_A(t)$, the backbone's `LinearPMap.semigroup`, as the limit of $e^{-tA_\lambda}$ as
$\lambda \to 0^+$ for every datum in $H$, as in Remark 4(b) and footnote 4 of the source. The
solution of Theorem 7.4 is $t \mapsto S_A(t) u_0$. On this route Step 6 of the source's proof, and
the use of Lemma 7.2 in the existence proof, are not needed; Lemma 7.2 is proved on its own, as in
the source.

## Conventions

* Functions of time are `u : ℝ → H`. The space $C^1([0, +\infty); H)$ is
  `ContDiffOn ℝ 1 u (Set.Ici 0)`.
* The space $C([0, +\infty); D(A))$ is the backbone's `LinearPMap.ContDiffOnPowDomain A 0 1 u
  (Set.Ici 0)`: $u$ lifts to a continuous map into `LinearPMap.PowDomain A 1`, which is $D(A)$ with
  the graph norm $(|v|^2 + |Av|^2)^{1/2}$ of footnote 2 of the source.
* The equation with its initial condition is the backbone's
  `LinearPMap.IsSolutionOn A u₀ (Set.Ici 0) u`. At $t = 0$ the derivative is the one-sided
  derivative within $[0, +\infty)$.

## Deviations from the source

* **Lemma 7.1** (generalization). The source assumes $w \in C^1([0, +\infty); H)$. This follows from
  the equation, because $A_\lambda$ is bounded, and is not assumed. See
  `Brezis.Chapter07.lemma_7_1`.

## Not formalized

* **Remark 3.** It is a discussion and makes no precise statement.
* **Remark 4(b), the counterexample.** The claim that the limit $u(t)$ may lie outside $D(A)$ for
  every $t > 0$ and be nowhere differentiable is a claim about a counterexample, which is not
  constructed.
* **Remark 5, the converse.** The Hille–Yosida generation theorem, that every continuous semigroup
  of contractions is $S_A$ for a unique maximal monotone $A$, is quoted from the literature without
  proof.
-/

open Filter Topology Set
open scoped InnerProductSpace

noncomputable section

namespace Brezis.Chapter07

/-! ### Theorem 7.3: the Cauchy–Lipschitz–Picard theorem -/

section CauchyLipschitzPicard

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Theorem 7.3** of [brezis2011functional] (Cauchy, Lipschitz, Picard). Let $E$ be a Banach space
and let $F : E \to E$ be a Lipschitz map, $\|Fu - Fv\| \le L \|u - v\|$ for all $u, v \in E$.
Then for every $u_0 \in E$ there is a unique $u \in C^1([0, +\infty); E)$ such that
$$\frac{du}{dt}(t) = F(u(t)) \quad \text{for } t \ge 0, \qquad u(0) = u_0.$$

The derivative at $t = 0$ is the one-sided derivative within $[0, +\infty)$. Uniqueness holds
among the $C^1$ solutions, on $[0, +\infty)$. The equation is the backbone's `ODE.IsSolutionOn`.
The source proves the theorem by a contraction argument with a weighted norm; the backbone glues
the solutions on compact intervals instead. -/
theorem theorem_7_3 {F : E → E} {L : ℝ} (hF : ∀ u v, ‖F u - F v‖ ≤ L * ‖u - v‖) (u₀ : E) :
    ∃ u : ℝ → E, ODE.IsSolutionOn (fun _ v => F v) 0 u₀ (Ici 0) u ∧ ContDiffOn ℝ 1 u (Ici 0) ∧
      ∀ v : ℝ → E, ODE.IsSolutionOn (fun _ v => F v) 0 u₀ (Ici 0) v →
        ContDiffOn ℝ 1 v (Ici 0) → EqOn v u (Ici 0) := by
  have hlip : LipschitzWith (Real.toNNReal L) F :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [dist_eq_norm, dist_eq_norm]
      exact (hF x y).trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal L) (norm_nonneg _))
  have hlip' : ∀ t ∈ Ici (0 : ℝ), LipschitzWith (Real.toNNReal L) ((fun _ v => F v) t) :=
    fun _ _ => hlip
  have hcont : ContinuousOn (Function.uncurry fun _ v => F v) (Ici (0 : ℝ) ×ˢ univ) :=
    (hlip.continuous.comp continuous_snd).continuousOn
  obtain ⟨u, ⟨hu, -⟩, -⟩ := ODE.existsUnique_isSolutionOn_Ici_of_lipschitz hcont hlip' u₀
  refine ⟨u, hu, ?_, fun v hv _ => ODE.isSolutionOn_unique_of_lipschitz_Ici hlip' hv hu⟩
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ici 0)]
  refine ⟨fun t ht => (hu.hasDerivWithinAt ht).differentiableWithinAt, fun h => by simp at h, ?_⟩
  rw [contDiffOn_zero]
  exact (hlip.continuous.comp_continuousOn hu.continuousOn).congr fun t ht =>
    (hu.hasDerivWithinAt ht).derivWithin (uniqueDiffOn_Ici 0 t ht)

end CauchyLipschitzPicard

/-! ### Theorem 7.4: the Hille–Yosida theorem -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {A : H →ₗ.[ℝ] H}

/-- **Problem (6)** of [brezis2011functional], the class of solutions. Let $A$ be a linear unbounded
operator on $H$ and $u_0 \in H$. A function $u : \mathbb{R} \to H$ is a **solution of problem
(6)** if
$$u \in C^1([0, +\infty); H) \cap C([0, +\infty); D(A)), \qquad \frac{du}{dt} + Au = 0 \text{ on
  } [0, +\infty), \qquad u(0) = u_0.$$

The equation and the initial condition are `LinearPMap.IsSolutionOn A u₀ (Set.Ici 0) u`: the
values $u(t)$, $t \ge 0$, lie in $D(A)$, the equation holds with the one-sided derivative at
$0$, and $u(0) = u_0$. The condition $u \in C([0, +\infty); D(A))$ is
`LinearPMap.ContDiffOnPowDomain A 0 1 u (Set.Ici 0)`: $u$ lifts to a continuous map into $D(A)$
with the graph norm $(|v|^2 + |Av|^2)^{1/2}$ of footnote 2, so $t \mapsto Au(t)$ is continuous
as well. -/
def IsSolution (A : H →ₗ.[ℝ] H) (u₀ : H) (u : ℝ → H) : Prop :=
  A.IsSolutionOn u₀ (Ici 0) u ∧ ContDiffOn ℝ 1 u (Ici 0) ∧ A.ContDiffOnPowDomain 0 1 u (Ici 0)

/-- The class $C^n(s; D(A^j))$ depends only on the values of $u$ on $s$: if $u \in C^n(s; D(A^j))$
and $u = v$ on $s$, then $v \in C^n(s; D(A^j))$.

This is the backbone's `LinearPMap.ContDiffOnPowDomain.congr`. -/
theorem contDiffOnPowDomain_congr {n : WithTop ℕ∞} {j : ℕ} {u v : ℝ → H} {s : Set ℝ}
    (h : A.ContDiffOnPowDomain n j u s) (huv : EqOn u v s) : A.ContDiffOnPowDomain n j v s :=
  h.congr huv

/-- The element $(u_0, Au_0)$ of $D(A)$ with the graph norm, for $u_0 \in D(A)$. -/
private def toPowDomainOne (A : H →ₗ.[ℝ] H) (u₀ : A.domain) : A.PowDomain 1 :=
  LinearPMap.PowDomain.mk A ![(u₀ : H), A u₀] fun i => by
    refine ⟨?_, ?_⟩ <;> simp [Fin.fin_one_eq_zero i]

variable [CompleteSpace H]

/-- Let $H$ be a Hilbert space, let $A$ be maximal monotone, and let $u_0 \in D(A)$. Then
$t \mapsto S_A(t) u_0$ is a solution of problem (6) in the sense of
`Brezis.Chapter07.IsSolution`.

This is the solution of Theorem 7.4. The condition $u \in C([0, +\infty); D(A))$ is Theorem 7.5
with $k = j = 1$. -/
theorem isSolution_semigroup (hA : IsMaximalMonotone A) (u₀ : A.domain) :
    IsSolution A u₀ fun t => A.semigroup t u₀ := by
  refine ⟨hA.isMaximalMonotone.isSolutionOn_semigroup u₀,
    hA.isMaximalMonotone.contDiffOn_semigroup_apply u₀, ?_⟩
  have h := hA.isMaximalMonotone.contDiffOnPowDomain_semigroup (toPowDomainOne A u₀) le_rfl
  simpa [toPowDomainOne] using h

/-- **Theorem 7.4** of [brezis2011functional] (Hille–Yosida). Let $H$ be a Hilbert space, let $A$ be
maximal monotone, and let $u_0 \in D(A)$. Then there is a unique
$$u \in C^1([0, +\infty); H) \cap C([0, +\infty); D(A))$$
with $du/dt + Au = 0$ on $[0, +\infty)$ and $u(0) = u_0$. Moreover, for all $t \ge 0$,
$$|u(t)| \le |u_0| \quad \text{and} \quad \left|\frac{du}{dt}(t)\right| = |Au(t)| \le |Au_0|.$$

Uniqueness means that every solution in the sense of `Brezis.Chapter07.IsSolution` agrees with
$u$ on $[0, +\infty)$. The derivative is `derivWithin u (Set.Ici 0) t`. The solution is
$t \mapsto S_A(t) u_0$. Steps 1–5 of the source's proof are the backbone results
`LinearPMap.IsMonotone.norm_sub_le_of_isSolutionOn`, `antitoneOn_norm_exp_neg_smul_apply`,
`LinearPMap.IsMaximalMonotone.norm_expYosida_sub_expYosida_le`,
`LinearPMap.IsMaximalMonotone.tendstoUniformlyOn_deriv_expYosida` and
`LinearPMap.IsMaximalMonotone.hasDerivWithinAt_semigroup_apply`; Step 6 is not needed on that
route. -/
theorem theorem_7_4 (hA : IsMaximalMonotone A) (u₀ : A.domain) :
    ∃ u : ℝ → H, ∃ hu : IsSolution A u₀ u, (∀ v, IsSolution A u₀ v → EqOn v u (Ici 0)) ∧
      (∀ t, 0 ≤ t → ‖u t‖ ≤ ‖(u₀ : H)‖) ∧
      ∀ t (ht : 0 ≤ t), ‖derivWithin u (Ici 0) t‖ = ‖A ⟨u t, hu.1.mem_domain t ht⟩‖ ∧
        ‖A ⟨u t, hu.1.mem_domain t ht⟩‖ ≤ ‖A u₀‖ := by
  refine ⟨fun t => A.semigroup t u₀, isSolution_semigroup hA u₀,
    fun v hv => hv.1.eq_semigroup hA.isMaximalMonotone,
    fun _ ht => hA.isMaximalMonotone.norm_semigroup_apply_le ht u₀, fun t ht => ⟨?_, ?_⟩⟩
  · rw [((hA.isMaximalMonotone.isSolutionOn_semigroup u₀).hasDerivWithinAt t ht).derivWithin
      (uniqueDiffOn_Ici 0 t ht), norm_neg]
  · exact hA.isMaximalMonotone.norm_apply_semigroup_apply_le u₀ ht

/-- **Lemma 7.1** of [brezis2011functional]. Let $H$ be a Hilbert space, let $A$ be maximal
monotone, and let $\lambda > 0$. Let $w : \mathbb{R} \to H$ satisfy
$$\frac{dw}{dt} + A_\lambda w = 0 \quad \text{on } [0, +\infty),$$
with the one-sided derivative at $0$. Then $t \mapsto |w(t)|$ is nonincreasing on
$[0, +\infty)$, $|dw/dt(t)| = |A_\lambda w(t)|$ for $t \ge 0$, and $t \mapsto |A_\lambda w(t)|$
is nonincreasing on $[0, +\infty)$.

**Generalization.** The source assumes $w \in C^1([0, +\infty); H)$. This follows from the
equation, because $A_\lambda$ is bounded, and is not assumed.

The derivative is `derivWithin w (Set.Ici 0) t`. Since $A_\lambda$ is a bounded monotone
operator (Proposition 7.2(e)), uniqueness gives $w(t) = e^{-tA_\lambda} w(0)$. Both claims then
follow from the backbone's `antitoneOn_norm_exp_neg_smul_apply`, the second one for the datum
$A_\lambda w(0)$, because $A_\lambda$ commutes with $e^{-tA_\lambda}$. -/
theorem lemma_7_1 (hA : IsMaximalMonotone A) {l : ℝ} (hl : 0 < l) {w : ℝ → H}
    (hw' : ∀ t, 0 ≤ t → HasDerivWithinAt w (-(yosidaApprox hA hl (w t))) (Ici 0) t) :
    AntitoneOn (fun t => ‖w t‖) (Ici 0) ∧
      (∀ t, 0 ≤ t → ‖derivWithin w (Ici 0) t‖ = ‖yosidaApprox hA hl (w t)‖) ∧
      AntitoneOn (fun t => ‖yosidaApprox hA hl (w t)‖) (Ici 0) := by
  simp only [yosidaApprox_eq] at hw' ⊢
  -- `A_λ` as an everywhere-defined monotone unbounded operator
  have hBm : ((A.yosida l : H →ₗ[ℝ] H).toPMap ⊤).IsMonotone := fun v => by
    change 0 ≤ RCLike.re ⟪A.yosida l (v : H), (v : H)⟫_ℝ
    simpa using hA.isMaximalMonotone.inner_yosida_nonneg hl (v : H)
  have hsol : ((A.yosida l : H →ₗ[ℝ] H).toPMap ⊤).IsSolutionOn (w 0) (Ici 0) w :=
    ⟨rfl, fun _ _ => Submodule.mem_top, fun t ht => hw' t ht⟩
  have hexp : ((A.yosida l : H →ₗ[ℝ] H).toPMap ⊤).IsSolutionOn (w 0) (Ici 0)
      fun t => A.expYosida l t (w 0) :=
    ⟨by simp [LinearPMap.expYosida_zero], fun _ _ => Submodule.mem_top, fun t _ =>
      (LinearPMap.hasDerivAt_expYosida_apply (A := A) l (w 0) t).hasDerivWithinAt⟩
  have hEq : EqOn w (fun t => A.expYosida l t (w 0)) (Ici 0) :=
    hBm.eqOn_of_isSolutionOn hsol hexp
  refine ⟨(hA.isMaximalMonotone.antitoneOn_norm_expYosida_apply hl (w 0)).congr fun t ht =>
    by simp only [hEq ht], fun t ht => ?_, ?_⟩
  · rw [(hw' t ht).derivWithin (uniqueDiffOn_Ici 0 t ht), norm_neg]
  · refine (hA.isMaximalMonotone.antitoneOn_norm_expYosida_apply hl (A.yosida l (w 0))).congr
      fun t ht => ?_
    simp only [hEq ht, LinearPMap.yosida_expYosida_comm]

/-- **Lemma 7.2** of [brezis2011functional]. Let $H$ be a Hilbert space, let $A$ be maximal
monotone, and let $u_0 \in D(A)$. Then for every $\varepsilon > 0$ there is
$\bar u_0 \in D(A^2)$, that is, $\bar u_0 \in D(A)$ with $A\bar u_0 \in D(A)$, such that
$$|u_0 - \bar u_0| < \varepsilon \quad \text{and} \quad |Au_0 - A\bar u_0| < \varepsilon.$$
So $D(A^2)$ is dense in $D(A)$ for the graph norm.

As in the source, the proof takes $\bar u_0 = J_\lambda u_0$ for small $\lambda > 0$. It applies
Proposition 7.2(c) to $u_0$ and to $Au_0$, using $J_\lambda(Au_0) = A(J_\lambda u_0)$. -/
theorem lemma_7_2 (hA : IsMaximalMonotone A) (u₀ : A.domain) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : A.domain, A v ∈ A.domain ∧ ‖(u₀ : H) - v‖ < ε ∧ ‖A u₀ - A v‖ < ε := by
  have h1 := (hA.isMaximalMonotone.tendsto_resolvent_apply (u₀ : H)).eventually
    (Metric.ball_mem_nhds _ hε)
  have h2 := (hA.isMaximalMonotone.tendsto_resolvent_apply (A u₀)).eventually
    (Metric.ball_mem_nhds _ hε)
  obtain ⟨l, ⟨hl1, hl2⟩, hl⟩ := ((h1.and h2).and self_mem_nhdsWithin).exists
  have hl' : (0 : ℝ) < l := hl
  refine ⟨⟨A.resolvent l u₀, hA.isMaximalMonotone.resolvent_apply_mem_domain hl' u₀⟩, ?_, ?_, ?_⟩
  · rw [← hA.isMaximalMonotone.resolvent_apply_comm hl' u₀]
    exact hA.isMaximalMonotone.resolvent_apply_mem_domain hl' _
  · have h := Metric.mem_ball.1 hl1
    rw [dist_eq_norm] at h
    rw [norm_sub_rev]
    exact h
  · have h := Metric.mem_ball.1 hl2
    rw [dist_eq_norm] at h
    rw [← hA.isMaximalMonotone.resolvent_apply_comm hl' u₀, norm_sub_rev]
    exact h

/-! ### Remarks 4–6 -/

/-- **Remark 4(a)** in Chapter 7 of [brezis2011functional]. Let $H$ be a Hilbert space, let $A$ be
maximal monotone, and let $u_0 \in D(A)$. For $\lambda > 0$ let
$u_\lambda(t) = e^{-tA_\lambda} u_0$. Then:

* $u_\lambda$ solves the approximate problem (7), $du_\lambda/dt + A_\lambda u_\lambda = 0$ on
  $\mathbb{R}$ and $u_\lambda(0) = u_0$;
* if $u$ is a solution of problem (6) in the sense of `Brezis.Chapter07.IsSolution`, then
  $u_\lambda \to u$ as $\lambda \to 0^+$, uniformly on $[0, T]$ for every $T$.

The function $u_\lambda(t)$ is the backbone's `LinearPMap.expYosida A l t u₀`. The source adds
that one can prove directly that the limit lies in $C^1([0, +\infty); H) \cap C([0, +\infty);
D(A))$ and satisfies (6); this is the route of the backbone. -/
theorem remark_7_4_a (hA : IsMaximalMonotone A) (u₀ : A.domain) :
    (∀ (l : ℝ) (hl : 0 < l), A.expYosida l 0 u₀ = u₀ ∧
      ∀ t, HasDerivAt (fun t => A.expYosida l t u₀)
        (-(yosidaApprox hA hl (A.expYosida l t u₀))) t) ∧
    ∀ u, IsSolution A u₀ u → ∀ T : ℝ,
      TendstoUniformlyOn (fun (l : ℝ) t => A.expYosida l t u₀) u (𝓝[>] 0) (Icc 0 T) := by
  refine ⟨fun l hl => ⟨by simp [LinearPMap.expYosida_zero], fun t => ?_⟩, fun u hu T => ?_⟩
  · rw [yosidaApprox_eq]
    exact LinearPMap.hasDerivAt_expYosida_apply (A := A) l u₀ t
  · exact (hA.isMaximalMonotone.tendstoUniformlyOn_expYosida_semigroup u₀).congr_right
      fun t ht => (hu.1.eq_semigroup hA.isMaximalMonotone ht.1).symm

/-- **Remark 4(b)** in Chapter 7 of [brezis2011functional], the convergence. Let $H$ be a Hilbert
space, let $A$ be maximal monotone, let $u_0 \in H$, and let $t \ge 0$. Then
$u_\lambda(t) = e^{-tA_\lambda} u_0$ converges in $H$ as $\lambda \to 0^+$.

The limit is the backbone's $S_A(t) u_0$, a "generalized" solution of problem (6) in the words
of the source. The further claim that this limit may lie outside $D(A)$ for every $t > 0$ and be
nowhere differentiable is about a counterexample and is not formalized; in the self-adjoint case
this cannot happen, by Theorem 7.7. -/
theorem remark_7_4_b (hA : IsMaximalMonotone A) (u₀ : H) {t : ℝ} (ht : 0 ≤ t) :
    ∃ w : H, Tendsto (fun l : ℝ => A.expYosida l t u₀) (𝓝[>] 0) (𝓝 w) :=
  ⟨A.semigroup t u₀, hA.isMaximalMonotone.tendsto_expYosida_semigroup ht u₀⟩

/-- **Remark 5** in Chapter 7 of [brezis2011functional] (contraction semigroups). Let $H$ be a
Hilbert space and let $A$ be maximal monotone. Then the operators $S_A(t) \in \mathcal{L}(H)$
satisfy:

* $S_A(t) u_0 = u(t)$ for $t \ge 0$, whenever $u_0 \in D(A)$ and $u$ is the solution of problem
  (6);
* (a) $\|S_A(t)\| \le 1$ for $t \ge 0$;
* (b) $S_A(t_1 + t_2) = S_A(t_1) \circ S_A(t_2)$ for $t_1, t_2 \ge 0$, and $S_A(0) = I$;
* (c) $|S_A(t) u_0 - u_0| \to 0$ as $t \to 0^+$, for every $u_0 \in H$.

So $(S_A(t))_{t \ge 0}$ is a continuous semigroup of contractions.

The source defines $S_A(t)$ as the extension by continuity of $u_0 \mapsto u(t)$ from the dense
set $D(A)$, which is possible because $|u(t)| \le |u_0|$. The backbone's `LinearPMap.semigroup`
is defined on all of $H$ directly, as in footnote 4 of the source. The converse, that every
continuous semigroup of contractions is $S_A$ for a unique maximal monotone $A$, is quoted from
the literature in the source and is not formalized. -/
theorem remark_7_5 (hA : IsMaximalMonotone A) :
    (∀ (u₀ : A.domain) (u : ℝ → H), IsSolution A u₀ u → ∀ t, 0 ≤ t → A.semigroup t u₀ = u t) ∧
      (∀ t : ℝ, 0 ≤ t → ‖A.semigroup t‖ ≤ 1) ∧
      ((∀ t₁ t₂ : ℝ, 0 ≤ t₁ → 0 ≤ t₂ →
        A.semigroup (t₁ + t₂) = (A.semigroup t₁).comp (A.semigroup t₂)) ∧ A.semigroup 0 = 1) ∧
      ∀ u₀ : H, Tendsto (fun t => ‖A.semigroup t u₀ - u₀‖) (𝓝[>] 0) (𝓝 0) :=
  ⟨fun _ _ hu _ ht => (hu.1.eq_semigroup hA.isMaximalMonotone ht).symm,
    fun _ ht => hA.isMaximalMonotone.norm_semigroup_le_one ht,
    ⟨fun _ _ h₁ h₂ => hA.isMaximalMonotone.semigroup_add h₁ h₂,
      hA.isMaximalMonotone.semigroup_zero⟩,
    fun u₀ => tendsto_iff_norm_sub_tendsto_zero.1
      (hA.isMaximalMonotone.tendsto_semigroup_apply_zero u₀)⟩

/-- **Remark 6** in Chapter 7 of [brezis2011functional]. Let $H$ be a Hilbert space, let $A$ be
maximal monotone, and let $\lambda \in \mathbb{R}$. Consider the problem
$$\frac{du}{dt} + Au + \lambda u = 0 \quad \text{on } [0, +\infty), \qquad u(0) = u_0.$$
Then:

* for every $u_0 \in H$, a function $u$ solves this problem if and only if
  $v(t) = e^{\lambda t} u(t)$ solves $dv/dt + Av = 0$ on $[0, +\infty)$, $v(0) = u_0$;
* for every $u_0 \in D(A)$, the function $u(t) = e^{-\lambda t} S_A(t) u_0$ solves the problem
  and is $C^1$ on $[0, +\infty)$, and every solution of the problem agrees with it on
  $[0, +\infty)$.

Both problems are stated with `LinearPMap.IsSolutionOn` on $[0, +\infty)$, which requires values
in $D(A)$ but no regularity class. The operator $A + \lambda I$ is `(l • LinearMap.id) +ᵥ A`,
with domain $D(A)$. The first part does not use the maximal monotonicity of $A$. -/
theorem remark_7_6 (hA : IsMaximalMonotone A) (l : ℝ) :
    (∀ (u₀ : H) (u : ℝ → H),
      ((l • LinearMap.id : H →ₗ[ℝ] H) +ᵥ A).IsSolutionOn u₀ (Ici 0) u ↔
        A.IsSolutionOn u₀ (Ici 0) fun t => Real.exp (l * t) • u t) ∧
    ∀ u₀ : A.domain,
      ((l • LinearMap.id : H →ₗ[ℝ] H) +ᵥ A).IsSolutionOn u₀ (Ici 0)
          (fun t => Real.exp (-(l * t)) • A.semigroup t u₀) ∧
        ContDiffOn ℝ 1 (fun t => Real.exp (-(l * t)) • A.semigroup t u₀) (Ici 0) ∧
        ∀ v, ((l • LinearMap.id : H →ₗ[ℝ] H) +ᵥ A).IsSolutionOn u₀ (Ici 0) v →
          EqOn v (fun t => Real.exp (-(l * t)) • A.semigroup t u₀) (Ici 0) := by
  refine ⟨fun _ _ => LinearPMap.isSolutionOn_smul_id_vadd_iff, fun u₀ => ⟨?_, ?_, fun v hv => ?_⟩⟩
  · rw [LinearPMap.isSolutionOn_smul_id_vadd_iff]
    convert hA.isMaximalMonotone.isSolutionOn_semigroup u₀ using 1
    funext t
    simp only [smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]
  · exact (by fun_prop : ContDiff ℝ 1 fun t : ℝ => Real.exp (-(l * t))).contDiffOn.smul
      (hA.isMaximalMonotone.contDiffOn_semigroup_apply u₀)
  · rw [LinearPMap.isSolutionOn_smul_id_vadd_iff] at hv
    intro t ht
    have h := hv.eq_semigroup hA.isMaximalMonotone ht
    simp only at h
    change v t = Real.exp (-(l * t)) • A.semigroup t u₀
    rw [← h, smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul]

end Brezis.Chapter07

end
