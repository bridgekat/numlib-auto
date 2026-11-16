/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.MetricSpace.Sequences
import Numlib.Analysis.Normed.Operator.BanachSteinhaus

/-!
# The Lax equivalence theorem

Let $V$ be a Banach space and let $L$ be a linear operator on $V$ with a dense domain $D(L)$, in
general unbounded. The abstract initial value problem is $u'(t) = L u(t)$ for $t \in [0, T]$,
$u(0) = u_0$. It is well posed if every $u_0 \in D(L)$ has a solution and any two solutions satisfy
$\|u(t) - \bar u(t)\| \le c_0 \|u_0 - \bar u_0\|$ on $[0, T]$. The solution map then extends to
bounded operators $S(t)$ on $V$, and $S(t) u_0$ for $u_0 \notin D(L)$ is the generalized solution. A
one-step scheme approximates $S$ by bounded operators $C(\Delta t)$: the discrete solution after $m$
steps is $C(\Delta t)^m u_0$.

The **Lax equivalence theorem** says that for a consistent scheme, stability and convergence are the
same thing: the powers $C(\Delta t)^m$ with $m \Delta t \le T$ are uniformly bounded if and only if
$C(\Delta t)^m u_0 \to S(t) u_0$ whenever $\Delta t \to 0$ and $m \Delta t \to t$. The module also
proves the order of convergence: a local error $O(\Delta t^{k+1})$ gives a global error
$O(\Delta t^k)$. The presentation follows Section 6.2 of [han2009theoretical] (Definitions 6.2.1,
6.2.2, 6.2.3, 6.2.7, 6.2.9 and 6.2.10, Propositions 6.2.5 and 6.2.6, Theorem 6.2.11 and Corollary
6.2.12). The theorem is due to [lax1956survey], and Chapter 3 of the book of Richtmyer and Morton is
the standard account.

## Main definitions

* `FiniteDifference.IsSolution`: a solution of $u' = L u$, $u(0) = u_0$ on $[0, T]$.
* `FiniteDifference.IsWellPosed`: well-posedness of the initial value problem on $[0, T]$ with
  stability constant $c_0$.
* `FiniteDifference.IsConsistent`: the local truncation error is $o(\Delta t)$ on a dense set of
  initial values.
* `FiniteDifference.IsStable`: the powers $C(\Delta t)^m$ with $m \Delta t \le T$ are bounded
  uniformly in $\Delta t$.
* `FiniteDifference.IsConvergent`: the discrete solution converges to $S(t) u_0$ along every
  refinement with $m \Delta t \to t$.

## Main results

* `FiniteDifference.exists_solutionOperator`: a well-posed problem with a dense domain has bounded
  solution operators $S(t)$ with $S(0) = 1$ and $\|S(t)\| \le c_0$.
* `FiniteDifference.solutionOperator_add`: the semigroup property $S(t_1 + t_0) = S(t_1) S(t_0)$.
* `FiniteDifference.continuousOn_of_dense`: a uniformly bounded family that is strongly continuous
  on a dense set of vectors is strongly continuous at every vector.
* `FiniteDifference.norm_iterate_sub_le`: the order of convergence, $\|C(\Delta t)^m u_0 - S(T)
  u_0\| \le M_0 T c \Delta t^k$ when $m \Delta t = T$.
* `FiniteDifference.isStable_iff_isConvergent`: the Lax equivalence theorem.

## Proof outline

Both directions rest on a telescoping identity. The discrete solution differs from the sampled exact
solution by the sum of the local errors, each propagated by a power of $C(\Delta t)$, so stability
bounds the global error by $M_0 (m \Delta t) \varepsilon$. For the forward direction, continuity of
$t \mapsto S(t) u_0$ then passes from $m \Delta t$ to $t$, and an $\varepsilon/3$ density argument
passes from the dense set on which consistency holds to all initial values. For the backward
direction, a uniform bound on $\|C(\Delta t)\|$ makes the step sizes bounded away from zero
harmless, so instability produces step sizes that tend to zero. The discrete times then have a
convergent subsequence, along which convergence bounds every orbit, and the uniform boundedness
principle bounds the operator norms. Both directions use the Banach–Steinhaus results of
`Numlib.Analysis.Normed.Operator.BanachSteinhaus`; this is the only reason why the theorem assumes
that $V$ is complete.

## Implementation notes

* A solution has its derivative *within* $[0, T]$. This gives the one-sided derivatives at the two
  endpoints, so no case split is needed.
* Uniqueness of the solution is not a separate assumption. It is the case $u_0 = \bar u_0$ of the
  stability bound of `FiniteDifference.IsWellPosed`, proved as `FiniteDifference.IsWellPosed.eqOn`.
* The equivalence theorem uses only $S(0) = 1$ and strong continuity of $t \mapsto S(t) u$ on
  $[0, T]$. So it is stated for an arbitrary family $S$ of bounded operators, not for the solution
  operators of $L$; `FiniteDifference.exists_solutionOperator` connects the two. This makes the
  theorem usable for any evolution family and keeps the theory of partially defined operators
  (`LinearPMap`) out of its proof. The semigroup property `FiniteDifference.solutionOperator_add` is
  proved because the sources state it, but it is not a hypothesis of any result here.
* Consistency, stability and convergence are propositions about the pair $(S, C)$, not structures
  that carry data.
* Consistency is stated with the division by $\Delta t$ cleared: $\|C(\Delta t) S(t) u_0 - S(t +
  \Delta t) u_0\| \le \varepsilon \Delta t$.
* Convergence quantifies over sequences of step sizes and step counts with $m \Delta t \to t$,
  because the limit is along an arbitrary refinement of the discrete time and not along one sequence
  of step sizes.
* The order of convergence `FiniteDifference.norm_iterate_sub_le` is an inequality with explicit
  constants, with no limit and no order symbol.
-/

open Filter Set Topology

/-- Let $E$ be a real normed space and let $Q$ be a bounded operator on $E$ with $\|Q\| \le 1$. Then
$\|Q^m\| \le 1$ for every $m \in \mathbb{N}$. -/
theorem ContinuousLinearMap.norm_pow_le_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Q : E →L[ℝ] E} (hQ : ‖Q‖ ≤ 1) (m : ℕ) : ‖Q ^ m‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [pow_zero]
    exact ContinuousLinearMap.norm_id_le
  · exact (norm_pow_le' Q hm).trans (pow_le_one₀ (norm_nonneg _) hQ)

namespace FiniteDifference

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-! ### The abstract initial value problem -/

section InitialValueProblem

variable [NormedSpace ℝ V]

/-- Let $L$ be a linear operator on $V$ with domain $D(L)$, let $T \in \mathbb{R}$ and $u_0 \in V$.
A curve $u : \mathbb{R} \to V$ is a **solution of the abstract initial value problem**
$u' = L u$, $u(0) = u_0$ on $[0, T]$ if $u(0) = u_0$ and, for every $t \in [0, T]$,
$u(t) \in D(L)$ and $u$ has the derivative $L u(t)$ at $t$ within $[0, T]$. This is Definition
6.2.1 and (6.2.2) of [han2009theoretical].

The derivative within the closed interval $[0, T]$ is the one-sided derivative at the two
endpoints, so the endpoints need no special case. The operator $L$ is a `LinearPMap`. -/
def IsSolution (L : V →ₗ.[𝕜] V) (T : ℝ) (u₀ : V) (u : ℝ → V) : Prop :=
  u 0 = u₀ ∧ ∀ t ∈ Icc (0 : ℝ) T, ∃ h : u t ∈ L.domain,
    HasDerivWithinAt u (L ⟨u t, h⟩) (Icc 0 T) t

/-- The abstract initial value problem for $L$ is **well posed** on $[0, T]$ with stability constant
$c_0$ if every initial value $u_0 \in D(L)$ has a solution on $[0, T]$
(`FiniteDifference.IsSolution`), and any two solutions $u$, $\bar u$ with initial values $u_0$,
$\bar u_0$ satisfy
$$\|u(t) - \bar u(t)\| \le c_0 \|u_0 - \bar u_0\| \qquad (t \in [0, T]).$$
This is Definition 6.2.2 and (6.2.3) of [han2009theoretical].

The second condition with $u_0 = \bar u_0$ is uniqueness of the solution on $[0, T]$
(`FiniteDifference.IsWellPosed.eqOn`), so uniqueness is not assumed separately. -/
def IsWellPosed (L : V →ₗ.[𝕜] V) (T c₀ : ℝ) : Prop :=
  (∀ u₀ ∈ L.domain, ∃ u, IsSolution L T u₀ u) ∧
    ∀ u₀ ū₀ u ū, IsSolution L T u₀ u → IsSolution L T ū₀ ū →
      ∀ t ∈ Icc (0 : ℝ) T, ‖u t - ū t‖ ≤ c₀ * ‖u₀ - ū₀‖

/-- Uniqueness of the solution: if the initial value problem for $L$ is well posed on $[0, T]$, then
two solutions with the same initial value agree on $[0, T]$. -/
theorem IsWellPosed.eqOn {L : V →ₗ.[𝕜] V} {T c₀ : ℝ} (hwp : IsWellPosed L T c₀) {u₀ : V}
    {u ū : ℝ → V} (hu : IsSolution L T u₀ u) (hū : IsSolution L T u₀ ū) :
    EqOn u ū (Icc 0 T) := by
  intro t ht
  have h := hwp.2 u₀ u₀ u ū hu hū t ht
  rw [sub_self, norm_zero, mul_zero] at h
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h)

/-- The constant zero curve solves the initial value problem with initial value $0$. -/
private theorem isSolution_zero (L : V →ₗ.[𝕜] V) (T : ℝ) : IsSolution L T 0 (fun _ => 0) := by
  refine ⟨rfl, fun t _ => ⟨L.domain.zero_mem, ?_⟩⟩
  have hz : (L ⟨(0 : V), L.domain.zero_mem⟩) = 0 := by
    rw [show (⟨(0 : V), L.domain.zero_mem⟩ : L.domain) = 0 from rfl]
    exact L.map_zero
  rw [hz]
  exact hasDerivWithinAt_const _ _ _

/-- The sum of two solutions is a solution, with the sum of the initial values. -/
private theorem isSolution_add {L : V →ₗ.[𝕜] V} {T : ℝ} {u₀ ū₀ : V} {u ū : ℝ → V}
    (hu : IsSolution L T u₀ u) (hū : IsSolution L T ū₀ ū) :
    IsSolution L T (u₀ + ū₀) (fun t => u t + ū t) := by
  refine ⟨by dsimp only; rw [hu.1, hū.1], fun t ht => ?_⟩
  obtain ⟨h1, hd1⟩ := hu.2 t ht
  obtain ⟨h2, hd2⟩ := hū.2 t ht
  refine ⟨L.domain.add_mem h1 h2, ?_⟩
  have hL : (L ⟨u t + ū t, L.domain.add_mem h1 h2⟩) = L ⟨u t, h1⟩ + L ⟨ū t, h2⟩ := by
    rw [show (⟨u t + ū t, L.domain.add_mem h1 h2⟩ : L.domain) = ⟨u t, h1⟩ + ⟨ū t, h2⟩ from rfl]
    exact L.map_add _ _
  rw [hL]
  exact HasDerivWithinAt.add hd1 hd2

/-- Let $u$ and $\bar u$ be solutions of the initial value problem for $L$ on $[0, T]$ with initial
values $u_0$ and $\bar u_0$. Then $u - \bar u$ is a solution with initial value
$u_0 - \bar u_0$. -/
theorem IsSolution.sub {L : V →ₗ.[𝕜] V} {T : ℝ} {u₀ ū₀ : V} {u ū : ℝ → V}
    (hu : IsSolution L T u₀ u) (hū : IsSolution L T ū₀ ū) :
    IsSolution L T (u₀ - ū₀) (u - ū) := by
  refine ⟨by rw [Pi.sub_apply, hu.1, hū.1], fun t ht => ?_⟩
  obtain ⟨h1, hd1⟩ := hu.2 t ht
  obtain ⟨h2, hd2⟩ := hū.2 t ht
  exact ⟨L.domain.sub_mem h1 h2, (hd1.sub hd2).congr_deriv (L.map_sub ⟨u t, h1⟩ ⟨ū t, h2⟩).symm⟩

/-- The **semigroup property**. Let $L$ be a linear operator on $V$ with a dense domain $D(L)$, let
$T \in \mathbb{R}$, and assume that every $u_0 \in D(L)$ has a solution on $[0, T]$. Let
$S : \mathbb{R} \to \mathcal{L}(V)$ be a family of bounded operators that represents the
solutions at every horizon $T' \in [0, T]$: for $t \in [0, T']$, $u_0 \in D(L)$ and every
solution $u$ on $[0, T']$ with initial value $u_0$, $S(t) u_0 = u(t)$. Then for $t_0, t_1 \ge 0$
with $t_1 + t_0 \le T$,
$$S(t_1 + t_0) = S(t_1) S(t_0).$$
This is Proposition 6.2.6 of [han2009theoretical].

The proof uses the time-translation invariance of the equation and the uniqueness of solutions.
The family $S$ must represent the solutions at every horizon $T' \le T$, not only at $T$:
translating a solution back by $t_0$ gives a solution on $[0, T - t_0]$, and it is the
representation on that interval that identifies it with the solution started at $S(t_0) u_0$. A
statement about the horizon $T$ alone says nothing about curves that are defined only on a
shorter interval. The Lax equivalence theorem `FiniteDifference.isStable_iff_isConvergent` does
not use this property, and it must not become one of its hypotheses; it is proved here because
the sources state it. -/
theorem solutionOperator_add {L : V →ₗ.[𝕜] V} (hdense : Dense (L.domain : Set V)) {T : ℝ}
    {S : ℝ → V →L[𝕜] V} (hex : ∀ u₀ ∈ L.domain, ∃ u, IsSolution L T u₀ u)
    (hS : ∀ T' ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T', ∀ u₀ ∈ L.domain, ∀ u,
      IsSolution L T' u₀ u → S t u₀ = u t)
    {t₀ t₁ : ℝ} (ht₀ : 0 ≤ t₀) (ht₁ : 0 ≤ t₁) (hsum : t₁ + t₀ ≤ T) :
    S (t₁ + t₀) = S t₁ ∘L S t₀ := by
  have hT : (0 : ℝ) ≤ T := le_trans (by linarith) hsum
  have hTT : T ∈ Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
  have key : EqOn (S (t₁ + t₀)) (S t₁ ∘L S t₀) (L.domain : Set V) := by
    intro u₀ hu₀
    obtain ⟨u, hu⟩ := hex u₀ hu₀
    have h1 : S (t₁ + t₀) u₀ = u (t₁ + t₀) :=
      hS T hTT _ ⟨by linarith, hsum⟩ u₀ hu₀ u hu
    have h2 : S t₀ u₀ = u t₀ := hS T hTT _ ⟨ht₀, by linarith⟩ u₀ hu₀ u hu
    obtain ⟨hmem, -⟩ := hu.2 t₀ ⟨ht₀, by linarith⟩
    -- the solution translated back by `t₀`, on the horizon `T - t₀`
    have hw : IsSolution L (T - t₀) (u t₀) (fun τ => u (τ + t₀)) := by
      refine ⟨by norm_num, fun τ hτ => ?_⟩
      obtain ⟨h, hd⟩ := hu.2 (τ + t₀) ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
      refine ⟨h, ?_⟩
      have hshift : HasDerivWithinAt (fun ρ : ℝ => ρ + t₀) 1 (Icc 0 (T - t₀)) τ := by
        simpa using (hasDerivWithinAt_id τ (Icc 0 (T - t₀))).add_const t₀
      have hmaps : MapsTo (fun ρ : ℝ => ρ + t₀) (Icc 0 (T - t₀)) (Icc 0 T) := fun ρ hρ =>
        ⟨by linarith [hρ.1], by linarith [hρ.2]⟩
      have hcomp : HasDerivWithinAt (u ∘ fun ρ : ℝ => ρ + t₀)
          ((1 : ℝ) • (L ⟨u (τ + t₀), h⟩)) (Icc 0 (T - t₀)) τ :=
        HasDerivWithinAt.scomp τ hd hshift hmaps
      rw [one_smul] at hcomp
      exact hcomp
    have h3 : S t₁ (u t₀) = u (t₁ + t₀) :=
      hS (T - t₀) ⟨by linarith, by linarith⟩ t₁ ⟨ht₁, by linarith⟩ (u t₀) hmem _ hw
    rw [ContinuousLinearMap.comp_apply, h2, h3, h1]
  exact DFunLike.coe_injective
    (Continuous.ext_on hdense (S (t₁ + t₀)).continuous (S t₁ ∘L S t₀).continuous key)

section Smul

variable [SMulCommClass ℝ 𝕜 V]

/-- A scalar multiple of a solution is a solution, with the scalar multiple of the initial value. -/
private theorem isSolution_smul {L : V →ₗ.[𝕜] V} {T : ℝ} {u₀ : V} {u : ℝ → V}
    (hu : IsSolution L T u₀ u) (c : 𝕜) : IsSolution L T (c • u₀) (fun t => c • u t) := by
  refine ⟨by dsimp only; rw [hu.1], fun t ht => ?_⟩
  obtain ⟨h1, hd1⟩ := hu.2 t ht
  refine ⟨L.domain.smul_mem c h1, ?_⟩
  have hL : (L ⟨c • u t, L.domain.smul_mem c h1⟩) = c • L ⟨u t, h1⟩ := by
    rw [show (⟨c • u t, L.domain.smul_mem c h1⟩ : L.domain) = c • ⟨u t, h1⟩ from rfl]
    exact L.map_smul c _
  rw [hL]
  exact HasDerivWithinAt.const_smul c hd1

/-- **The solution operators.** Let $V$ be a Banach space, let $L$ be a linear operator on $V$ with
a dense domain $D(L)$, let $T \ge 0$ and $c_0 \ge 0$, and let the initial value problem for $L$
be well posed on $[0, T]$ with stability constant $c_0$. Then there is a family
$S : \mathbb{R} \to \mathcal{L}(V)$ of bounded operators with $S(0) = 1$, $\|S(t)\| \le c_0$ for
$t \in [0, T]$, and $S(t) u_0 = u(t)$ for $t \in [0, T]$, $u_0 \in D(L)$ and every solution $u$
on $[0, T]$ with initial value $u_0$. The value $S(t) u_0$ at an initial value $u_0 \notin D(L)$
is the **generalized solution** of Definition 6.2.3 of [han2009theoretical].

The solution map at time $t$ is linear on $D(L)$, because sums and scalar multiples of solutions
are solutions and the solution is unique. It is bounded by $c_0$, by comparison with the zero
solution. So it extends uniquely to $V$ along the dense inclusion of $D(L)$; the extension
theorem that the source cites is `ContinuousLinearMap.extend`. The family is defined for every
real $t$ by clamping $t$ into $[0, T]$, which is why every clause about it has the hypothesis
$t \in [0, T]$. -/
theorem exists_solutionOperator [CompleteSpace V] (L : V →ₗ.[𝕜] V)
    (hdense : Dense (L.domain : Set V)) {T c₀ : ℝ} (hT : 0 ≤ T) (hc₀ : 0 ≤ c₀)
    (hwp : IsWellPosed L T c₀) :
    ∃ S : ℝ → V →L[𝕜] V, S 0 = 1 ∧ (∀ t ∈ Icc (0 : ℝ) T, ‖S t‖ ≤ c₀) ∧
      ∀ t ∈ Icc (0 : ℝ) T, ∀ u₀ ∈ L.domain, ∀ u, IsSolution L T u₀ u → S t u₀ = u t := by
  classical
  choose sol hsol using hwp.1
  have hval : ∀ t ∈ Icc (0 : ℝ) T, ∀ (u₀ : V) (h : u₀ ∈ L.domain) (u : ℝ → V),
      IsSolution L T u₀ u → sol u₀ h t = u t :=
    fun t ht u₀ h u hu => hwp.eqOn (hsol u₀ h) hu ht
  -- clamping the parameter into `Icc 0 T` makes the solution map linear for *every* parameter
  have hclmem : ∀ t : ℝ, max 0 (min t T) ∈ Icc (0 : ℝ) T := fun t =>
    ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
  have hclid : ∀ t ∈ Icc (0 : ℝ) T, max 0 (min t T) = t := fun t ht => by
    rw [min_eq_left ht.2, max_eq_right ht.1]
  obtain ⟨g, hgapp⟩ : ∃ g : ℝ → (L.domain →ₗ[𝕜] V),
      ∀ (t : ℝ) (x : L.domain), g t x = sol (x : V) x.2 (max 0 (min t T)) :=
    ⟨fun t =>
      { toFun := fun x => sol (x : V) x.2 (max 0 (min t T))
        map_add' := fun x y =>
          hval _ (hclmem t) ((x : V) + (y : V)) (L.domain.add_mem x.2 y.2) _
            (isSolution_add (hsol _ x.2) (hsol _ y.2))
        map_smul' := fun c x =>
          hval _ (hclmem t) (c • (x : V)) (L.domain.smul_mem c x.2) _
            (isSolution_smul (hsol _ x.2) c) }, fun _ _ => rfl⟩
  have hgb : ∀ (t : ℝ) (x : L.domain), ‖g t x‖ ≤ c₀ * ‖x‖ := by
    intro t x
    have h := hwp.2 (x : V) 0 (sol (x : V) x.2) (fun _ => 0) (hsol _ x.2) (isSolution_zero L T)
      _ (hclmem t)
    rw [hgapp]
    simpa using h
  obtain ⟨G, hGapp, hGnorm⟩ : ∃ G : ℝ → (L.domain →L[𝕜] V),
      (∀ (t : ℝ) (x : L.domain), G t x = g t x) ∧ ∀ t : ℝ, ‖G t‖ ≤ c₀ :=
    ⟨fun t => (g t).mkContinuous c₀ (hgb t), fun _ _ => rfl,
      fun t => LinearMap.mkContinuous_norm_le _ hc₀ _⟩
  have hdr : DenseRange (L.domain.subtypeL : L.domain →L[𝕜] V) := by
    have hrange : Set.range (L.domain.subtypeL : L.domain →L[𝕜] V) = (L.domain : Set V) :=
      Subtype.range_coe
    rw [DenseRange, hrange]
    exact hdense
  have hbd : ∀ x : L.domain, ‖x‖ ≤ (1 : NNReal) * ‖L.domain.subtypeL x‖ := by
    intro x
    simp
  have hui : IsUniformInducing (L.domain.subtypeL : L.domain →L[𝕜] V) :=
    (ContinuousLinearMap.isUniformEmbedding_of_bound _ hbd).isUniformInducing
  have hext : ∀ (t : ℝ) (v : V) (hv : v ∈ L.domain),
      ContinuousLinearMap.extend (G t) L.domain.subtypeL v = sol v hv (max 0 (min t T)) := by
    intro t v hv
    have h := ContinuousLinearMap.extend_eq (G t) hdr hui ⟨v, hv⟩
    rw [hGapp, hgapp] at h
    exact h
  refine ⟨fun t => ContinuousLinearMap.extend (G t) L.domain.subtypeL, ?_, fun t _ => ?_, ?_⟩
  · refine DFunLike.coe_injective (Continuous.ext_on hdense
      (ContinuousLinearMap.extend (G 0) L.domain.subtypeL).continuous
      (1 : V →L[𝕜] V).continuous fun v hv => ?_)
    have h0 : max 0 (min (0 : ℝ) T) = 0 := by rw [min_eq_left hT, max_self]
    rw [hext 0 v hv, h0, (hsol v hv).1]
    rfl
  · exact le_trans (by simpa using ContinuousLinearMap.opNorm_extend_le (G t) hdr hbd) (hGnorm t)
  · intro t ht u₀ hu₀ u hu
    rw [hext t u₀ hu₀, hclid t ht]
    exact hval t ht u₀ hu₀ u hu

end Smul

end InitialValueProblem

/-! ### Strong continuity of a uniformly bounded family -/

/-- Let $D \subseteq V$ be dense, let $P \subseteq \mathbb{R}$, and let
$S : \mathbb{R} \to \mathcal{L}(V)$ be a family of bounded operators with $\|S(t)\| \le c_0$ for
$t \in P$. If $t \mapsto S(t) u$ is continuous on $P$ for every $u \in D$, then
$t \mapsto S(t) u$ is continuous on $P$ for every $u \in V$. So the generalized solution is
continuous in time, although only the genuine solutions are assumed differentiable. This is
Proposition 6.2.5 of [han2009theoretical].

The statement is for an arbitrary set $P$ of parameters, not only for $[0, T]$. It is an
instance of the Banach–Steinhaus density criterion
`ContinuousLinearMap.tendsto_of_tendsto_on_dense_of_bounded`, and uses neither completeness nor
a Baire category argument. -/
theorem continuousOn_of_dense {D : Set V} (hD : Dense D) {S : ℝ → V →L[𝕜] V} {P : Set ℝ} {c₀ : ℝ}
    (hb : ∀ t ∈ P, ‖S t‖ ≤ c₀) (hcont : ∀ u ∈ D, ContinuousOn (fun t => S t u) P) (u : V) :
    ContinuousOn (fun t => S t u) P := by
  rw [continuousOn_iff_continuous_domRestrict]
  refine continuous_iff_continuousAt.2 fun t₀ => ?_
  have hrestrict : ∀ v ∈ D, Tendsto (fun t : ↥P => S (t : ℝ) v) (𝓝 t₀) (𝓝 (S (t₀ : ℝ) v)) :=
    fun v hv => (continuous_iff_continuousAt.1 (hcont v hv).domRestrict) t₀
  exact ContinuousLinearMap.tendsto_of_tendsto_on_dense_of_bounded hD
    (fun t : ↥P => hb (t : ℝ) t.2) hrestrict u

/-! ### Consistency, stability and convergence -/

/-- Let $S, C : \mathbb{R} \to \mathcal{L}(V)$ be families of bounded operators, let
$T, \Delta_0 \in \mathbb{R}$ and $D \subseteq V$. The scheme $C$ is **consistent** with the
evolution family $S$ on $[0, T]$, for step sizes in $(0, \Delta_0]$, on the set $D$ of initial
values, if $D$ is dense and for every $u_0 \in D$ and $\varepsilon > 0$ there is $\delta > 0$
such that
$$\|C(\Delta t) S(t) u_0 - S(t + \Delta t) u_0\| \le \varepsilon \Delta t$$
for all $\Delta t \in (0, \Delta_0]$ with $\Delta t < \delta$ and all $t \in [0, T]$ with
$t + \Delta t \le T$. That is, the local truncation error is $o(\Delta t)$ uniformly in $t$.
This is Definition 6.2.7 of [han2009theoretical].

The division by $\Delta t$ is cleared, so that no $\Delta t^{-1}$ occurs. The family $S$ is
evaluated only within the horizon, at $t + \Delta t \le T$: an evolution family is known on
$[0, T]$ only, and the proof of the Lax theorem uses the truncation error only at the grid
points $k \Delta t$ with $(k + 1) \Delta t \le m \Delta t \le T$. -/
def IsConsistent (S C : ℝ → V →L[𝕜] V) (T Δ₀ : ℝ) (D : Set V) : Prop :=
  Dense D ∧ ∀ u₀ ∈ D, ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ Δt ∈ Ioc (0 : ℝ) Δ₀, Δt < δ →
    ∀ t ∈ Icc (0 : ℝ) T, t + Δt ≤ T → ‖C Δt (S t u₀) - S (t + Δt) u₀‖ ≤ ε * Δt

/-- A scheme $C : \mathbb{R} \to \mathcal{L}(V)$ is **stable** on $[0, T]$ for step sizes in
$(0, \Delta_0]$ if there is $M_0$ with
$$\|C(\Delta t)^m\| \le M_0 \qquad \text{for all } \Delta t \in (0, \Delta_0] \text{ and } m \in
  \mathbb{N} \text{ with } m \Delta t \le T.$$
This is Definition 6.2.10 of [han2009theoretical].

The power is taken in the monoid of bounded operators. -/
def IsStable (C : ℝ → V →L[𝕜] V) (T Δ₀ : ℝ) : Prop :=
  ∃ M₀ : ℝ, ∀ Δt ∈ Ioc (0 : ℝ) Δ₀, ∀ m : ℕ, (m : ℝ) * Δt ≤ T → ‖C Δt ^ m‖ ≤ M₀

/-- A scheme $C$ is **convergent** to the evolution family $S$ on $[0, T]$ for step sizes in
$(0, \Delta_0]$ if for every $t \in [0, T]$, every $u_0 \in V$, every sequence of step sizes
$\Delta t_i \in (0, \Delta_0]$ and every sequence of step counts $m_i \in \mathbb{N}$ with
$m_i \Delta t_i \le T$, $\Delta t_i \to 0$ and $m_i \Delta t_i \to t$,
$$\|C(\Delta t_i)^{m_i} u_0 - S(t) u_0\| \to 0 \qquad (i \to \infty).$$
This is Definition 6.2.9 of [han2009theoretical].

The definition quantifies over sequences because the limit is along an arbitrary refinement
whose discrete time tends to $t$, not along a single sequence of step sizes. -/
def IsConvergent (S C : ℝ → V →L[𝕜] V) (T Δ₀ : ℝ) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) T, ∀ u₀ : V, ∀ (Δt : ℕ → ℝ) (m : ℕ → ℕ), (∀ i, Δt i ∈ Ioc (0 : ℝ) Δ₀) →
    (∀ i, (m i : ℝ) * Δt i ≤ T) → Tendsto Δt atTop (𝓝 0) →
    Tendsto (fun i => (m i : ℝ) * Δt i) atTop (𝓝 t) →
    Tendsto (fun i => ‖(C (Δt i) ^ m i) u₀ - S t u₀‖) atTop (𝓝 0)

/-- If $\|C(\Delta t)\| \le 1$ for every $\Delta t \in (0, \Delta_0]$, then the scheme $C$ is stable
with $M_0 = 1$ on every horizon $T$. -/
theorem isStable_of_forall_norm_le_one {C : ℝ → V →L[𝕜] V} {Δ₀ : ℝ}
    (hC : ∀ Δt ∈ Set.Ioc (0 : ℝ) Δ₀, ‖C Δt‖ ≤ 1) (T : ℝ) : IsStable C T Δ₀ := by
  refine ⟨1, fun Δt hΔt m _ => ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [pow_zero]
    exact ContinuousLinearMap.norm_id_le
  · exact (norm_pow_le' _ hm).trans (pow_le_one₀ (norm_nonneg _) (hC Δt hΔt))

/-! ### The telescoping estimate -/

/-- The telescoping estimate: if $\|C^i\| \le M_0$ for $i \le m$ and
$\|C v_i - v_{i+1}\| \le \delta$ for $i < m$, then $\|C^m v_0 - v_m\| \le m M_0 \delta$. -/
private theorem norm_iterate_sub_le_aux (C : V →L[𝕜] V) (M₀ δ : ℝ) :
    ∀ (m : ℕ) (v : ℕ → V), (∀ i ≤ m, ‖C ^ i‖ ≤ M₀) → (∀ i < m, ‖C (v i) - v (i + 1)‖ ≤ δ) →
      ‖(C ^ m) (v 0) - v m‖ ≤ m * (M₀ * δ) := by
  intro m
  induction m with
  | zero => intro v _ _; simp
  | succ n ih =>
    intro v hC hloc
    have hpow : (C ^ (n + 1)) (v 0) = (C ^ n) (C (v 0)) := by rw [pow_succ]; rfl
    have hstep : (C ^ (n + 1)) (v 0) - v (n + 1)
        = (C ^ n) (C (v 0) - v 1) + ((C ^ n) (v 1) - v (n + 1)) := by
      rw [map_sub, hpow]
      abel
    have hM : 0 ≤ M₀ := le_trans (norm_nonneg _) (hC n (Nat.le_succ n))
    have h1 : ‖(C ^ n) (C (v 0) - v 1)‖ ≤ M₀ * δ :=
      ((C ^ n).le_opNorm _).trans (mul_le_mul (hC n (Nat.le_succ n)) (hloc 0 (Nat.succ_pos n))
        (norm_nonneg _) hM)
    have h2 : ‖(C ^ n) ((fun i => v (i + 1)) 0) - (fun i => v (i + 1)) n‖ ≤ n * (M₀ * δ) :=
      ih (fun i => v (i + 1)) (fun i hi => hC i (hi.trans (Nat.le_succ n)))
        (fun i hi => hloc (i + 1) (Nat.succ_lt_succ hi))
    rw [hstep]
    calc ‖(C ^ n) (C (v 0) - v 1) + ((C ^ n) (v 1) - v (n + 1))‖
        ≤ ‖(C ^ n) (C (v 0) - v 1)‖ + ‖(C ^ n) (v 1) - v (n + 1)‖ := norm_add_le _ _
      _ ≤ M₀ * δ + n * (M₀ * δ) := add_le_add h1 h2
      _ = (n + 1 : ℕ) * (M₀ * δ) := by push_cast; ring

/-- The telescoping estimate on the grid of step $\Delta t$: if $S(0) = 1$, $\|C^i\| \le M_0$ for
$i \le m$ and every local error $\|C S(i \Delta t) u_0 - S(i \Delta t + \Delta t) u_0\|$ with
$i < m$ is at most $\delta$, then $\|C^m u_0 - S(m \Delta t) u_0\| \le m M_0 \delta$. -/
private theorem norm_iterate_sub_le_grid {S : ℝ → V →L[𝕜] V} {C : V →L[𝕜] V} (hS0 : S 0 = 1)
    (M₀ δ Δt : ℝ) (u₀ : V) (m : ℕ) (hC : ∀ i ≤ m, ‖C ^ i‖ ≤ M₀)
    (hloc : ∀ i < m, ‖C (S ((i : ℝ) * Δt) u₀) - S ((i : ℝ) * Δt + Δt) u₀‖ ≤ δ) :
    ‖(C ^ m) u₀ - S ((m : ℝ) * Δt) u₀‖ ≤ m * (M₀ * δ) := by
  have hgrid : ∀ i < m, ‖C ((fun j : ℕ => S ((j : ℝ) * Δt) u₀) i)
      - (fun j : ℕ => S ((j : ℝ) * Δt) u₀) (i + 1)‖ ≤ δ := by
    intro i hi
    have hcast : ((i + 1 : ℕ) : ℝ) * Δt = (i : ℝ) * Δt + Δt := by push_cast; ring
    simpa only [hcast] using hloc i hi
  have h := norm_iterate_sub_le_aux C M₀ δ m (fun j : ℕ => S ((j : ℝ) * Δt) u₀) hC hgrid
  have hz : S (((0 : ℕ) : ℝ) * Δt) u₀ = u₀ := by
    rw [Nat.cast_zero, zero_mul, hS0]
    rfl
  rwa [hz] at h

/-- The **order of convergence**. Let $S, C : \mathbb{R} \to \mathcal{L}(V)$ be families of bounded
operators with $S(0) = 1$, let $\Delta t > 0$, $k, m \in \mathbb{N}$ with $m \Delta t = T$, and
let $u_0 \in V$. Assume that $\|C(\Delta t)^i\| \le M_0$ for $i \le m$, and that the local error
at $u_0$ satisfies
$$\|C(\Delta t) S(t) u_0 - S(t + \Delta t) u_0\| \le c\, \Delta t^{k+1} \qquad (t \in [0, T]).$$
Then
$$\|C(\Delta t)^m u_0 - S(T) u_0\| \le M_0 T c\, \Delta t^k.$$
This is Corollary 6.2.12 of [han2009theoretical].

The proof is the telescoping estimate with no limit taken, so the statement is an inequality
with explicit constants. -/
theorem norm_iterate_sub_le {S C : ℝ → V →L[𝕜] V} {T Δt c M₀ : ℝ} {k m : ℕ} (u₀ : V)
    (hS0 : S 0 = 1) (hΔt : 0 < Δt) (hmΔt : (m : ℝ) * Δt = T)
    (hstab : ∀ i ≤ m, ‖C Δt ^ i‖ ≤ M₀)
    (hloc : ∀ t ∈ Icc (0 : ℝ) T, ‖C Δt (S t u₀) - S (t + Δt) u₀‖ ≤ c * Δt ^ (k + 1)) :
    ‖(C Δt ^ m) u₀ - S T u₀‖ ≤ M₀ * T * c * Δt ^ k := by
  have hgrid : ‖(C Δt ^ m) u₀ - S ((m : ℝ) * Δt) u₀‖ ≤ m * (M₀ * (c * Δt ^ (k + 1))) := by
    refine norm_iterate_sub_le_grid hS0 M₀ (c * Δt ^ (k + 1)) Δt u₀ m hstab fun i hi => ?_
    refine hloc _ ⟨by positivity, ?_⟩
    rw [← hmΔt]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi.le) hΔt.le
  rw [← hmΔt]
  calc ‖(C Δt ^ m) u₀ - S ((m : ℝ) * Δt) u₀‖ ≤ m * (M₀ * (c * Δt ^ (k + 1))) := hgrid
    _ = M₀ * ((m : ℝ) * Δt) * c * Δt ^ k := by ring

/-! ### The Lax equivalence theorem -/

/-- If $\|A\| \le b$ with $b \ge 1$, then $\|A^m\| \le b^m$. -/
private theorem norm_pow_le_pow {A : V →L[𝕜] V} {b : ℝ} (hb : 1 ≤ b) (h : ‖A‖ ≤ b) (m : ℕ) :
    ‖A ^ m‖ ≤ b ^ m := by
  induction m with
  | zero =>
    simp only [pow_zero]
    calc ‖(1 : V →L[𝕜] V)‖ = ‖ContinuousLinearMap.id 𝕜 V‖ := rfl
      _ ≤ 1 := ContinuousLinearMap.norm_id_le
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (norm_mul_le _ _).trans
      (mul_le_mul ih h (norm_nonneg _) (le_trans zero_le_one (one_le_pow₀ hb)))

/-- Stability for small step sizes implies stability: if $\|C(\Delta t)\| \le c_1$ on
$(0, \Delta_0]$ and the powers within the horizon are bounded for step sizes in $(0, a]$ with
$a > 0$, then $C$ is stable, because step sizes in $[a, \Delta_0]$ allow only boundedly many
steps within the horizon. -/
private theorem isStable_of_isStable_below {C : ℝ → V →L[𝕜] V} {T Δ₀ c₁ a : ℝ}
    (ha : 0 < a) (hC : ∀ Δt ∈ Ioc (0 : ℝ) Δ₀, ‖C Δt‖ ≤ c₁)
    (h : ∃ M, ∀ Δt ∈ Ioc (0 : ℝ) a, ∀ m : ℕ, (m : ℝ) * Δt ≤ T → ‖C Δt ^ m‖ ≤ M) :
    IsStable C T Δ₀ := by
  obtain ⟨M, hM⟩ := h
  have hc₁ : (1 : ℝ) ≤ max c₁ 1 := le_max_right _ _
  refine ⟨max M (max c₁ 1 ^ ⌈T / a⌉₊), fun Δt hΔt m hm => ?_⟩
  rcases le_or_gt Δt a with hle | hgt
  · exact le_max_of_le_left (hM Δt ⟨hΔt.1, hle⟩ m hm)
  · have h1 : (m : ℝ) * a ≤ T :=
      le_trans (mul_le_mul_of_nonneg_left hgt.le (Nat.cast_nonneg _)) hm
    have h2 : (m : ℝ) ≤ (⌈T / a⌉₊ : ℝ) := ((le_div_iff₀ ha).2 h1).trans (Nat.le_ceil _)
    have hmle : m ≤ ⌈T / a⌉₊ := by exact_mod_cast h2
    refine le_max_of_le_right ?_
    exact (norm_pow_le_pow hc₁ ((hC Δt hΔt).trans (le_max_left _ _)) m).trans
      (pow_le_pow_right₀ hc₁ hmle)

/-- The **Lax equivalence theorem**. Let $V$ be a Banach space, let $T \ge 0$, and let
$S : \mathbb{R} \to \mathcal{L}(V)$ be a family of bounded operators with $S(0) = 1$ such that
$t \mapsto S(t) u$ is continuous on $[0, T]$ for every $u \in V$. Let
$C : \mathbb{R} \to \mathcal{L}(V)$ be a scheme with $\|C(\Delta t)\| \le c_1$ for every
$\Delta t \in (0, \Delta_0]$, and let $C$ be consistent with $S$ on $[0, T]$ on a dense set $D$
of initial values (`FiniteDifference.IsConsistent`). Then $C$ is stable on $[0, T]$
(`FiniteDifference.IsStable`) if and only if it is convergent to $S$ on $[0, T]$
(`FiniteDifference.IsConvergent`). This is Theorem 6.2.11 of [han2009theoretical].

The uniform bound $\|C(\Delta t)\| \le c_1$ is necessary and does not follow from the other
hypotheses. The sources use it without stating it when they introduce the family; without it,
the case of a bounded number of steps in the backward direction has no proof. The semigroup
property of $S$ is not used.

The forward direction telescopes the error over the grid and uses the Banach–Steinhaus density
criterion, whose uniform bound is stability; the backward direction uses the uniform boundedness
principle along a subsequence of step sizes that tend to zero. -/
theorem isStable_iff_isConvergent [CompleteSpace V] {S C : ℝ → V →L[𝕜] V} {T Δ₀ c₁ : ℝ}
    {D : Set V} (hT : 0 ≤ T) (hS0 : S 0 = 1)
    (hScont : ∀ u : V, ContinuousOn (fun t => S t u) (Icc 0 T))
    (hC : ∀ Δt ∈ Ioc (0 : ℝ) Δ₀, ‖C Δt‖ ≤ c₁) (hcons : IsConsistent S C T Δ₀ D) :
    IsStable C T Δ₀ ↔ IsConvergent S C T Δ₀ := by
  constructor
  · -- stability and consistency give convergence
    rintro ⟨M₀, hM₀⟩
    have hMnn : (0 : ℝ) ≤ max M₀ 0 := le_max_right _ _
    have hM : ∀ Δt ∈ Ioc (0 : ℝ) Δ₀, ∀ m : ℕ, (m : ℝ) * Δt ≤ T → ‖C Δt ^ m‖ ≤ max M₀ 0 :=
      fun Δt hΔt m hm => (hM₀ Δt hΔt m hm).trans (le_max_left _ _)
    have hP : (0 : ℝ) ≤ max M₀ 0 * T := mul_nonneg hMnn hT
    have hden : (0 : ℝ) < 2 * (max M₀ 0 * T + 1) := by linarith
    intro t ht u₀ Δt m hΔt hmT hΔt0 hmt
    -- on the dense set, the telescoping estimate and strong continuity of `S`
    have hdense : ∀ v ∈ D, Tendsto (fun i => (C (Δt i) ^ m i) v) atTop (𝓝 (S t v)) := by
      intro v hv
      refine Metric.tendsto_atTop.2 fun ε' hε' => ?_
      have hεpos : (0 : ℝ) < ε' / (2 * (max M₀ 0 * T + 1)) := div_pos hε' hden
      obtain ⟨δ, hδ, hloc⟩ := hcons.2 v hv (ε' / (2 * (max M₀ 0 * T + 1))) hεpos
      have hA : ∀ᶠ i in atTop, Δt i < δ := by
        simpa using hΔt0.eventually (eventually_lt_nhds hδ)
      have hB : ∀ᶠ i in atTop, ‖S ((m i : ℝ) * Δt i) v - S t v‖ < ε' / 2 := by
        have hmem : ∀ i, (m i : ℝ) * Δt i ∈ Icc (0 : ℝ) T := fun i =>
          ⟨mul_nonneg (Nat.cast_nonneg _) (hΔt i).1.le, hmT i⟩
        have hwithin : Tendsto (fun i => (m i : ℝ) * Δt i) atTop (𝓝[Icc 0 T] t) :=
          tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hmt
            (Eventually.of_forall hmem)
        have hlim : Tendsto (fun i => S ((m i : ℝ) * Δt i) v) atTop (𝓝 (S t v)) :=
          (hScont v t ht).tendsto.comp hwithin
        have hconst : Tendsto (fun _ : ℕ => S t v) atTop (𝓝 (S t v)) := tendsto_const_nhds
        have hz := (hlim.sub hconst).norm
        simp only [sub_self, norm_zero] at hz
        exact hz.eventually (eventually_lt_nhds (by linarith))
      rw [← Filter.eventually_atTop]
      filter_upwards [hA, hB] with i hAi hBi
      have hgrid : ‖(C (Δt i) ^ m i) v - S ((m i : ℝ) * Δt i) v‖
          ≤ m i * (max M₀ 0 * (ε' / (2 * (max M₀ 0 * T + 1)) * Δt i)) := by
        refine norm_iterate_sub_le_grid hS0 (max M₀ 0) (ε' / (2 * (max M₀ 0 * T + 1)) * Δt i)
          (Δt i) v (m i) (fun k hk => ?_) fun k hk => ?_
        · refine hM (Δt i) (hΔt i) k ?_
          exact le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (hΔt i).1.le) (hmT i)
        · have hk1 : ((k : ℝ) + 1) * Δt i ≤ T :=
            le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (hΔt i).1.le) (hmT i)
          refine hloc (Δt i) (hΔt i) hAi _
            ⟨mul_nonneg (Nat.cast_nonneg _) (hΔt i).1.le, ?_⟩ (by linarith)
          exact le_trans (by nlinarith [(hΔt i).1.le]) hk1
      have hbound : m i * (max M₀ 0 * (ε' / (2 * (max M₀ 0 * T + 1)) * Δt i)) < ε' / 2 := by
        have hexp : (m i : ℝ) * (max M₀ 0 * (ε' / (2 * (max M₀ 0 * T + 1)) * Δt i))
            = (max M₀ 0 * ((m i : ℝ) * Δt i)) * (ε' / (2 * (max M₀ 0 * T + 1))) := by ring
        have h1 : max M₀ 0 * ((m i : ℝ) * Δt i) ≤ max M₀ 0 * T :=
          mul_le_mul_of_nonneg_left (hmT i) hMnn
        have h3 : max M₀ 0 * T * (ε' / (2 * (max M₀ 0 * T + 1))) < ε' / 2 := by
          have hne : (max M₀ 0 * T + 1) ≠ 0 := ne_of_gt (by linarith)
          have key : ε' / 2 - max M₀ 0 * T * (ε' / (2 * (max M₀ 0 * T + 1)))
              = ε' / (2 * (max M₀ 0 * T + 1)) := by
            field_simp
            ring
          linarith [hεpos, key]
        rw [hexp]
        exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right h1 hεpos.le) h3
      have htri : ‖(C (Δt i) ^ m i) v - S t v‖
          ≤ ‖(C (Δt i) ^ m i) v - S ((m i : ℝ) * Δt i) v‖ + ‖S ((m i : ℝ) * Δt i) v - S t v‖ := by
        have h := norm_add_le ((C (Δt i) ^ m i) v - S ((m i : ℝ) * Δt i) v)
          (S ((m i : ℝ) * Δt i) v - S t v)
        rwa [sub_add_sub_cancel] at h
      rw [dist_eq_norm]
      calc ‖(C (Δt i) ^ m i) v - S t v‖
          ≤ ‖(C (Δt i) ^ m i) v - S ((m i : ℝ) * Δt i) v‖
            + ‖S ((m i : ℝ) * Δt i) v - S t v‖ := htri
        _ < ε' / 2 + ε' / 2 := add_lt_add (hgrid.trans_lt hbound) hBi
        _ = ε' := by ring
    -- and then everywhere, by the density criterion
    have hall : Tendsto (fun i => (C (Δt i) ^ m i) u₀) atTop (𝓝 (S t u₀)) :=
      ContinuousLinearMap.tendsto_of_tendsto_on_dense_of_bounded hcons.1
        (fun i => hM (Δt i) (hΔt i) (m i) (hmT i)) hdense u₀
    have hconst : Tendsto (fun _ : ℕ => S t u₀) atTop (𝓝 (S t u₀)) := tendsto_const_nhds
    have hz := (hall.sub hconst).norm
    simp only [sub_self, norm_zero] at hz
    exact hz
  · -- convergence gives stability
    intro hconv
    rcases le_or_gt Δ₀ 0 with hΔ₀ | hΔ₀
    · exact ⟨0, fun Δt hΔt => absurd (lt_of_lt_of_le hΔt.1 (hΔt.2.trans hΔ₀)) (lt_irrefl 0)⟩
    by_contra hns
    -- instability at every scale of step size
    have hsmall : ∀ k : ℕ, ∃ Δt : ℝ, Δt ∈ Ioc (0 : ℝ) Δ₀ ∧ Δt ≤ 1 / (k + 1) ∧
        ∃ mm : ℕ, (mm : ℝ) * Δt ≤ T ∧ (k : ℝ) < ‖C Δt ^ mm‖ := by
      intro k
      by_contra hcon
      push Not at hcon
      refine hns (isStable_of_isStable_below (a := min Δ₀ (1 / (k + 1)))
        (lt_min hΔ₀ (by positivity)) hC ⟨(k : ℝ), fun Δt hΔt mm hm => ?_⟩)
      exact hcon Δt ⟨hΔt.1, hΔt.2.trans (min_le_left _ _)⟩ (hΔt.2.trans (min_le_right _ _)) mm hm
    choose Δt hΔtmem hΔtsmall m hmT hnorm using hsmall
    -- the step sizes tend to zero and the discrete times have a convergent subsequence
    have hΔt0 : Tendsto Δt atTop (𝓝 0) := by
      refine squeeze_zero (fun k => (hΔtmem k).1.le) hΔtsmall ?_
      simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hmem : ∀ k, (m k : ℝ) * Δt k ∈ Icc (0 : ℝ) T := fun k =>
      ⟨mul_nonneg (Nat.cast_nonneg _) (hΔtmem k).1.le, hmT k⟩
    obtain ⟨t, ht, φ, hφ, hφlim⟩ :=
      (isCompact_Icc (a := (0 : ℝ)) (b := T)).tendsto_subseq hmem
    -- along it, convergence bounds every orbit, so uniform boundedness bounds the norms
    have hbdd : BddAbove (Set.range fun k => ‖C (Δt (φ k)) ^ m (φ k)‖) := by
      by_contra hnb
      obtain ⟨v, hv⟩ := ContinuousLinearMap.exists_not_tendsto_of_not_bddAbove hnb (S t)
      refine hv (tendsto_iff_norm_sub_tendsto_zero.2 ?_)
      exact hconv t ht v (fun k => Δt (φ k)) (fun k => m (φ k)) (fun k => hΔtmem (φ k))
        (fun k => hmT (φ k)) (hΔt0.comp hφ.tendsto_atTop) hφlim
    obtain ⟨M, hMbd⟩ := hbdd
    obtain ⟨k, hk⟩ := exists_nat_gt M
    refine absurd (hMbd ⟨k, rfl⟩) (not_le.2 ?_)
    exact lt_of_lt_of_le hk (le_trans (by exact_mod_cast hφ.le_apply) (hnorm (φ k)).le)

end FiniteDifference
