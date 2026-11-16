/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Numlib.Analysis.Calculus.SpaceTime

/-!
# The classical maximum principle for the heat equation

Let $E$ be a finite-dimensional real inner product space, let $\Omega \subseteq E$ be open and
bounded, and let $\nu > 0$ and $T > 0$. This module proves the parabolic maximum principle, Theorem
10.6 of [brezis2011functional], for a function $u(x, t)$ that is continuous on
$\overline{\Omega} \times [0, T]$, differentiable in $t$ and of class $C^2$ in $x$ on
$\Omega \times (0, T)$, and satisfies $\partial_t u - \nu \Delta u \le 0$ there: the maximum of $u$
over $\overline{\Omega} \times [0, T]$ is attained on the parabolic boundary
$$P = (\overline{\Omega} \times \{0\}) \cup (\partial \Omega \times [0, T]).$$
The source treats the case $\nu = 1$. For a solution of $\partial_t u = \nu \Delta u$ that vanishes
on $\partial \Omega \times [0, T]$, the principle applied to $u$ and $-u$ gives $|u(x, t)| \le
\max_{\overline{\Omega}} |u(\cdot, 0)|$.

The module also proves Remark 4 of chapter 10 of [brezis2011functional]: if a solution is $C^\infty$
and vanishes on the lateral boundary, then its initial datum $u_0 = u(\cdot, 0)$ satisfies the
compatibility conditions $\Delta^j u_0 = 0$ on $\partial \Omega$ for every $j$. No Sobolev space is
used in this module.

## Main definitions

* `Heat.parabolicBoundary`: the parabolic boundary $P$ of the cylinder $\Omega \times (0, T)$.
* `Heat.IsClassicalSubsolution`: the hypotheses (20)–(22) of Theorem 10.6 of [brezis2011functional],
  with $\partial_t u - \nu \Delta u \le 0$ on the open cylinder.
* `Heat.IsClassicalSolution`: the same regularity, with $\partial_t u = \nu \Delta u$ on the open
  cylinder.

## Main results

* `Heat.mem_parabolicBoundary_of_isMaxOn_of_lt`: a strict subsolution, with
  $\partial_t v - \nu \Delta v < 0$, attains its maximum over $\overline{\Omega} \times [0, T']$
  only on the parabolic boundary.
* `Heat.IsClassicalSubsolution.le_of_le_on_parabolicBoundary`: Theorem 10.6 as a bound: if $u \le M$
  on $P$, then $u \le M$ on $\overline{\Omega} \times [0, T]$.
* `Heat.IsClassicalSubsolution.exists_isMaxOn_parabolicBoundary`: Theorem 10.6 as the existence of a
  maximum point on $P$, for nonempty $\Omega$.
* `Heat.IsClassicalSolution.abs_le_of_eq_zero_frontier`: a solution that vanishes on the lateral
  boundary satisfies $|u(x, t)| \le M$ whenever $|u(\cdot, 0)| \le M$ on $\overline{\Omega}$.
* `Heat.IsClassicalSolution.timeDeriv_iterate_eqOn`: a smooth solution satisfies
  $\partial_t^j u = \nu^j \Delta^j u$ on the open cylinder.
* `Heat.IsClassicalSolution.iteratedLaplacian_eq_zero_frontier`: Remark 4, the necessity of the
  compatibility conditions $\Delta^j u_0 = 0$ on $\partial \Omega$.

## Proof outline

For $\varepsilon > 0$ the function $v = u - \varepsilon t$ is a strict subsolution. At a maximum
point $(x_0, t_0)$ of $v$ with $x_0 \in \Omega$ and $t_0 > 0$, the Laplacian of $v$ in $x$ is at
most $0$ and the one-sided time derivative is at least $0$, which contradicts
$\partial_t v - \nu \Delta v < 0$. Hence $v$ attains its maximum on $P$, so
$u \le M + \varepsilon T$, and $\varepsilon \to 0$ gives the bound. As in footnote 8 of
[brezis2011functional], the argument runs on $[0, T']$ with $T' < T$, where $v$ is differentiable in
$t$ up to the right endpoint; the bound at $t = T$ then follows by continuity. Remark 4 follows from
the iterated equation $\partial_t^j u = \nu^j \Delta^j u$, which rests on the commutation
$\partial_t \Delta_x = \Delta_x \partial_t$ on smooth functions.

## Implementation notes

* A function of space and time is uncurried, $u : E \times \mathbb{R} \to \mathbb{R}$. Applications
  take $E = $ `EuclideanSpace ℝ (Fin N)`. The Laplacian is Mathlib's `InnerProductSpace.laplacian`,
  and $\partial \Omega$ is `frontier Ω`.
* The diffusion constant $\nu$ is a parameter because `AtkinsonHan.Chapter06.example_6_2_4` uses the
  equation $u_t = \nu u_{xx}$.
* The source asks that $u$ be of class $C^1$ in $t$ and $C^2$ in $x$. `Heat.IsClassicalSubsolution`
  asks only for differentiability in $t$ and $C^2$ at each point in $x$, which is all that the proof
  uses.
* The source perturbs $u$ by $\varepsilon |x|^2$. The perturbation $u - \varepsilon t$ used here has
  $\partial_t v - \nu \Delta v \le -\varepsilon < 0$ in every dimension, including $\dim E = 0$,
  where $\Delta |x|^2 = 0$. It needs no computation of $\Delta |x|^2$ and uses the same limit
  $\varepsilon \to 0$.
* The partial operators $\partial_t$ and $\Delta_x$ on functions of $(x, t)$ are `Heat.timeDeriv`
  and `Heat.spaceLaplacian` of `Numlib.Analysis.Calculus.SpaceTime`.
-/

open Filter Set Topology InnerProductSpace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace Heat

/-! ### The parabolic boundary -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The **parabolic boundary** of the cylinder $\Omega \times (0, T)$ is the set
$$P = (\overline{\Omega} \times \{0\}) \cup (\partial \Omega \times [0, T]),$$
the bottom and the lateral surface of the cylinder, without the top. It is the set of Theorem
10.6 of [brezis2011functional]. -/
def parabolicBoundary (Ω : Set E) (T : ℝ) : Set (E × ℝ) :=
  closure Ω ×ˢ {0} ∪ frontier Ω ×ˢ Icc 0 T

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- If $T \ge 0$, the parabolic boundary of $\Omega \times (0, T)$ lies in the closed cylinder
$\overline{\Omega} \times [0, T]$. -/
theorem parabolicBoundary_subset {Ω : Set E} {T : ℝ} (hT : 0 ≤ T) :
    parabolicBoundary Ω T ⊆ closure Ω ×ˢ Icc 0 T := by
  rintro ⟨x, t⟩ (⟨hx, ht⟩ | ⟨hx, ht⟩)
  · exact ⟨hx, by simp only [mem_singleton_iff] at ht; rw [ht]; exact ⟨le_rfl, hT⟩⟩
  · exact ⟨frontier_subset_closure hx, ht⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- If $T' \le T$, the parabolic boundary for the horizon $T'$ is contained in the parabolic
boundary for the horizon $T$. -/
theorem parabolicBoundary_mono {Ω : Set E} {T T' : ℝ} (h : T' ≤ T) :
    parabolicBoundary Ω T' ⊆ parabolicBoundary Ω T :=
  union_subset_union_right _ (prod_mono_right (Icc_subset_Icc_right h))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The parabolic boundary of $\Omega \times (0, T)$ is closed, for every set $\Omega$ and every
$T$. -/
theorem isClosed_parabolicBoundary (Ω : Set E) (T : ℝ) : IsClosed (parabolicBoundary Ω T) :=
  (isClosed_closure.prod isClosed_singleton).union (isClosed_frontier.prod isClosed_Icc)

/-- If $\Omega$ is bounded, then the parabolic boundary of $\Omega \times (0, T)$ is compact, for
every $T$. -/
theorem isCompact_parabolicBoundary {Ω : Set E} (hb : Bornology.IsBounded Ω) (T : ℝ) :
    IsCompact (parabolicBoundary Ω T) :=
  (hb.isCompact_closure.prod isCompact_singleton).union
    ((hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure).prod
      isCompact_Icc)

/-! ### Classical subsolutions and solutions -/

/-- Let $\nu, T \in \mathbb{R}$ and $\Omega \subseteq E$. A function
$u : E \times \mathbb{R} \to \mathbb{R}$ is a **classical subsolution of the heat equation**
$\partial_t u - \nu \Delta u \le 0$ on $\Omega \times (0, T)$ if it satisfies the hypotheses
(20)–(22) of Theorem 10.6 of [brezis2011functional]: $u$ is continuous on
$\overline{\Omega} \times [0, T]$; at every point $(x, t) \in \Omega \times (0, T)$ the function
$s \mapsto u(x, s)$ is differentiable at $t$ and the function $y \mapsto u(y, t)$ is of class
$C^2$ at $x$; and at every such point
$$\partial_t u(x, t) - \nu \Delta u(\cdot, t)(x) \le 0.$$

The source asks that $u$ be of class $C^1$ in $t$ and $C^2$ in $x$. This structure asks for less
continuity, which is all that the proof of Theorem 10.6 uses. -/
structure IsClassicalSubsolution (ν : ℝ) (Ω : Set E) (T : ℝ) (u : E × ℝ → ℝ) : Prop where
  /-- The function $u$ is continuous on the closed cylinder $\overline{\Omega} \times [0, T]$. -/
  continuousOn : ContinuousOn u (closure Ω ×ˢ Icc 0 T)
  /-- At every point $(x, t)$ of $\Omega \times (0, T)$, the function $s \mapsto u(x, s)$ is
  differentiable at $t$. -/
  differentiableAt_snd : ∀ x ∈ Ω, ∀ t ∈ Ioo 0 T, DifferentiableAt ℝ (fun s ↦ u (x, s)) t
  /-- At every point $(x, t)$ of $\Omega \times (0, T)$, the function $y \mapsto u(y, t)$ is of
  class $C^2$ at $x$. -/
  contDiffAt_fst : ∀ x ∈ Ω, ∀ t ∈ Ioo 0 T, ContDiffAt ℝ 2 (fun y ↦ u (y, t)) x
  /-- At every point $(x, t)$ of $\Omega \times (0, T)$, the inequality $\partial_t u(x, t) - \nu
  \Delta u(\cdot, t)(x) \le 0$ holds. -/
  deriv_sub_laplacian_nonpos : ∀ x ∈ Ω, ∀ t ∈ Ioo 0 T,
    deriv (fun s ↦ u (x, s)) t - ν * Δ (fun y ↦ u (y, t)) x ≤ 0

/-- Let $\nu, T \in \mathbb{R}$ and $\Omega \subseteq E$. A function
$u : E \times \mathbb{R} \to \mathbb{R}$ is a **classical solution of the heat equation**
$\partial_t u = \nu \Delta u$ on $\Omega \times (0, T)$ if $u$ is continuous on
$\overline{\Omega} \times [0, T]$, and at every point $(x, t) \in \Omega \times (0, T)$ the
function $s \mapsto u(x, s)$ is differentiable at $t$, the function $y \mapsto u(y, t)$ is of
class $C^2$ at $x$, and
$$\partial_t u(x, t) = \nu \Delta u(\cdot, t)(x).$$

No boundary condition and no initial condition is part of the definition. The regularity is that
of `Heat.IsClassicalSubsolution`. -/
structure IsClassicalSolution (ν : ℝ) (Ω : Set E) (T : ℝ) (u : E × ℝ → ℝ) : Prop where
  /-- The function $u$ is continuous on the closed cylinder $\overline{\Omega} \times [0, T]$. -/
  continuousOn : ContinuousOn u (closure Ω ×ˢ Icc 0 T)
  /-- At every point $(x, t)$ of $\Omega \times (0, T)$, the function $s \mapsto u(x, s)$ is
  differentiable at $t$. -/
  differentiableAt_snd : ∀ x ∈ Ω, ∀ t ∈ Ioo 0 T, DifferentiableAt ℝ (fun s ↦ u (x, s)) t
  /-- At every point $(x, t)$ of $\Omega \times (0, T)$, the function $y \mapsto u(y, t)$ is of
  class $C^2$ at $x$. -/
  contDiffAt_fst : ∀ x ∈ Ω, ∀ t ∈ Ioo 0 T, ContDiffAt ℝ 2 (fun y ↦ u (y, t)) x
  /-- At every point $(x, t)$ of $\Omega \times (0, T)$, the heat equation
  $\partial_t u(x, t) = \nu \Delta u(\cdot, t)(x)$ holds. -/
  deriv_eq_laplacian : ∀ x ∈ Ω, ∀ t ∈ Ioo 0 T,
    deriv (fun s ↦ u (x, s)) t = ν * Δ (fun y ↦ u (y, t)) x

variable {ν T : ℝ} {Ω : Set E} {u : E × ℝ → ℝ}

/-- A classical solution of $\partial_t u = \nu \Delta u$ on $\Omega \times (0, T)$ is a classical
subsolution on $\Omega \times (0, T)$. -/
theorem IsClassicalSolution.isClassicalSubsolution (hu : IsClassicalSolution ν Ω T u) :
    IsClassicalSubsolution ν Ω T u :=
  ⟨hu.continuousOn, hu.differentiableAt_snd, hu.contDiffAt_fst, fun x hx t ht =>
    (sub_eq_zero.2 (hu.deriv_eq_laplacian x hx t ht)).le⟩

/-- If $u$ is a classical solution of $\partial_t u = \nu \Delta u$ on $\Omega \times (0, T)$, then
so is $-u$. -/
theorem IsClassicalSolution.neg (hu : IsClassicalSolution ν Ω T u) :
    IsClassicalSolution ν Ω T (-u) := by
  refine ⟨hu.continuousOn.neg, fun x hx t ht => (hu.differentiableAt_snd x hx t ht).neg,
    fun x hx t ht => (hu.contDiffAt_fst x hx t ht).neg, fun x hx t ht => ?_⟩
  have h1 : (fun s ↦ (-u) (x, s)) = -(fun s ↦ u (x, s)) := rfl
  have h2 : (fun y ↦ (-u) (y, t)) = -(fun y ↦ u (y, t)) := rfl
  rw [h1, h2, deriv.neg, laplacian_neg, Pi.neg_apply, hu.deriv_eq_laplacian x hx t ht, mul_neg]

/-! ### The maximum principle -/

/-- **A strict subsolution attains its maximum only on the parabolic boundary.** Let
$\Omega \subseteq E$ be open, let $\nu > 0$ and $T' \in \mathbb{R}$, and let
$v : E \times \mathbb{R} \to \mathbb{R}$. Assume that at every point
$(x, t) \in \Omega \times (0, T']$ (the right endpoint included) the function
$s \mapsto v(x, s)$ is differentiable at $t$, the function $y \mapsto v(y, t)$ is of class $C^2$
at $x$, and
$$\partial_t v(x, t) - \nu \Delta v(\cdot, t)(x) < 0.$$
If $p \in \overline{\Omega} \times [0, T']$ is a maximum point of $v$ on
$\overline{\Omega} \times [0, T']$, then $p$ lies on the parabolic boundary of
$\Omega \times (0, T')$.

At a maximum point $(x_0, t_0)$ with $x_0 \in \Omega$ and $t_0 > 0$, the Laplacian in $x$ is at
most $0$ by `IsLocalMax.laplacian_nonpos`. The function $t \mapsto v(x_0, t)$ has a local
maximum at $t_0$ among $t \in [0, T']$, and $-t_0$ lies in the positive tangent cone of
$[0, T']$ at $t_0$, so the time derivative is at least $0$ by
`IsLocalMaxOn.hasFDerivWithinAt_nonpos`. This treats the cases $t_0 < T'$ and $t_0 = T'$ of the
source together. Then $\partial_t v - \nu \Delta v \ge 0$ at $(x_0, t_0)$, a contradiction. -/
theorem mem_parabolicBoundary_of_isMaxOn_of_lt (hΩ : IsOpen Ω) (hν : 0 < ν) {v : E × ℝ → ℝ}
    {T' : ℝ} (hd : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T', DifferentiableAt ℝ (fun s ↦ v (x, s)) t)
    (hx : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T', ContDiffAt ℝ 2 (fun y ↦ v (y, t)) x)
    (hlt : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T', deriv (fun s ↦ v (x, s)) t - ν * Δ (fun y ↦ v (y, t)) x < 0)
    {p : E × ℝ} (hp : p ∈ closure Ω ×ˢ Icc 0 T') (hmax : IsMaxOn v (closure Ω ×ˢ Icc 0 T') p) :
    p ∈ parabolicBoundary Ω T' := by
  obtain ⟨x₀, t₀⟩ := p
  obtain ⟨hx₀, ht₀⟩ := hp
  by_contra hnot
  simp only [parabolicBoundary, mem_union, mem_prod, mem_singleton_iff, not_or, not_and] at hnot
  have hx₀Ω : x₀ ∈ Ω := by
    have : x₀ ∈ closure Ω \ frontier Ω := ⟨hx₀, fun h => hnot.2 h ht₀⟩
    rwa [closure_sdiff_frontier, hΩ.interior_eq] at this
  have ht₀pos : 0 < t₀ := lt_of_le_of_ne ht₀.1 fun h => hnot.1 hx₀ h.symm
  have ht₀' : t₀ ∈ Ioc 0 T' := ⟨ht₀pos, ht₀.2⟩
  -- the Laplacian in `x` is `≤ 0` at the maximum
  have hΔ : Δ (fun y ↦ v (y, t₀)) x₀ ≤ 0 := by
    refine IsLocalMax.laplacian_nonpos ?_ (hx x₀ hx₀Ω t₀ ht₀')
    exact eventually_of_mem (hΩ.mem_nhds hx₀Ω) fun y hy => hmax ⟨subset_closure hy, ht₀⟩
  -- the time derivative is `≥ 0` at the maximum (one-sided, from the left)
  have hderiv : 0 ≤ deriv (fun s ↦ v (x₀, s)) t₀ := by
    have hmaxOn : IsMaxOn (fun s ↦ v (x₀, s)) (Icc 0 T') t₀ := fun s hs => hmax ⟨hx₀, hs⟩
    have hmax' : IsLocalMaxOn (fun s ↦ v (x₀, s)) (Icc 0 T') t₀ := hmaxOn.isLocalMaxOn
    have hseg : (-t₀ : ℝ) ∈ posTangentConeAt (Icc 0 T') t₀ := by
      refine mem_posTangentConeAt_of_segment_subset ?_
      rw [add_neg_cancel]
      exact (convex_Icc 0 T').segment_subset ht₀ ⟨le_rfl, ht₀.2.trans' ht₀.1⟩
    have h := hmax'.hasFDerivWithinAt_nonpos
      (hd x₀ hx₀Ω t₀ ht₀').hasDerivAt.hasFDerivAt.hasFDerivWithinAt hseg
    rw [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at h
    nlinarith
  have := hlt x₀ hx₀Ω t₀ ht₀'
  nlinarith [mul_nonneg hν.le (neg_nonneg.2 hΔ)]

/-- **The parabolic maximum principle**, bound form. Let $\Omega \subseteq E$ be open and bounded,
and let $\nu > 0$ and $T > 0$. Let $u$ be a classical subsolution of
$\partial_t u - \nu \Delta u \le 0$ on $\Omega \times (0, T)$, and let $M \in \mathbb{R}$ with
$u \le M$ on the parabolic boundary of $\Omega \times (0, T)$. Then $u \le M$ on
$\overline{\Omega} \times [0, T]$. This is Theorem 10.6 of [brezis2011functional].

For $t < T$ and $\varepsilon > 0$, the strict subsolution $v = u - \varepsilon t$ on $[0, T']$,
with $t \le T' < T$, attains its maximum on the parabolic boundary by
`Heat.mem_parabolicBoundary_of_isMaxOn_of_lt`. There $v \le u \le M$, hence
$u(x, t) \le M + \varepsilon T$, and $\varepsilon \to 0$ gives the bound. The bound at $t = T$
follows by continuity (`ContinuousWithinAt.closure_le`). -/
theorem IsClassicalSubsolution.le_of_le_on_parabolicBoundary (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hν : 0 < ν) (hT : 0 < T) (hu : IsClassicalSubsolution ν Ω T u)
    {M : ℝ} (hM : ∀ p ∈ parabolicBoundary Ω T, u p ≤ M) :
    ∀ q ∈ closure Ω ×ˢ Icc 0 T, u q ≤ M := by
  -- first on `closure Ω ×ˢ Ico 0 T`, by the perturbation `u - ε t` on `[0, T']`, `T' < T`
  have key : ∀ q ∈ closure Ω ×ˢ Ico 0 T, u q ≤ M := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    refine le_of_forall_pos_le_add fun ε hε => ?_
    set ε' := ε / T with hε'
    have hε'pos : 0 < ε' := by positivity
    set T' := (t + T) / 2 with hT'
    have hT'pos : 0 < T' := by rw [hT']; linarith [ht.1]
    have hT'T : T' < T := by rw [hT']; linarith [ht.2]
    have htT' : t ≤ T' := by rw [hT']; linarith [ht.2]
    have hK : IsCompact (closure Ω ×ˢ Icc 0 T') := hb.isCompact_closure.prod isCompact_Icc
    have hKne : (closure Ω ×ˢ Icc 0 T').Nonempty := ⟨(x, t), hx, ht.1, htT'⟩
    have hsub : closure Ω ×ˢ Icc 0 T' ⊆ closure Ω ×ˢ Icc 0 T :=
      prod_mono_right (Icc_subset_Icc_right hT'T.le)
    have hvc : ContinuousOn (fun p : E × ℝ ↦ u p - ε' * p.2) (closure Ω ×ˢ Icc 0 T') :=
      (hu.continuousOn.mono hsub).sub (continuous_const.mul continuous_snd).continuousOn
    obtain ⟨p, hp, hpmax⟩ := hK.exists_isMaxOn hKne hvc
    have hpP : p ∈ parabolicBoundary Ω T' := by
      refine mem_parabolicBoundary_of_isMaxOn_of_lt hΩ hν ?_ ?_ ?_ hp hpmax
      · intro y hy s hs
        exact (hu.differentiableAt_snd y hy s ⟨hs.1, hs.2.trans_lt hT'T⟩).sub
          ((differentiableAt_id).const_mul ε')
      · intro y hy s hs
        exact (hu.contDiffAt_fst y hy s ⟨hs.1, hs.2.trans_lt hT'T⟩).sub
          (contDiffAt_const (c := ε' * s))
      · intro y hy s hs
        have hs' : s ∈ Ioo 0 T := ⟨hs.1, hs.2.trans_lt hT'T⟩
        have h1 : deriv (fun r ↦ u (y, r) - ε' * r) s = deriv (fun r ↦ u (y, r)) s - ε' := by
          have hsum : HasDerivAt (fun r ↦ u (y, r) - ε' * r)
              (deriv (fun r ↦ u (y, r)) s - ε' * 1) s :=
            (hu.differentiableAt_snd y hy s hs').hasDerivAt.sub ((hasDerivAt_id s).const_mul ε')
          rw [mul_one] at hsum
          exact hsum.deriv
        have h2 : Δ (fun z ↦ u (z, s) - ε' * s) y = Δ (fun z ↦ u (z, s)) y := by
          have hsub' : (fun z ↦ u (z, s) - ε' * s) = (fun z ↦ u (z, s)) - fun _ ↦ ε' * s := rfl
          rw [hsub', (hu.contDiffAt_fst y hy s hs').laplacian_sub contDiffAt_const,
            laplacian_const, Pi.zero_apply, sub_zero]
        change deriv (fun r ↦ u (y, r) - ε' * r) s - ν * Δ (fun z ↦ u (z, s) - ε' * s) y < 0
        rw [h1, h2]
        linarith [hu.deriv_sub_laplacian_nonpos y hy s hs']
    have hvp : u p - ε' * p.2 ≤ M := by
      have hp0 : 0 ≤ p.2 := (parabolicBoundary_subset hT'pos.le hpP).2.1
      calc u p - ε' * p.2 ≤ u p := by nlinarith
        _ ≤ M := hM p (parabolicBoundary_mono hT'T.le hpP)
    have hvq : u (x, t) - ε' * t ≤ u p - ε' * p.2 := hpmax ⟨hx, ht.1, htT'⟩
    rw [hε'] at hvq hvp
    calc u (x, t) = (u (x, t) - ε / T * t) + ε / T * t := by ring
      _ ≤ M + ε / T * T := by
          have : ε / T * t ≤ ε / T * T := by gcongr; exact ht.2.le
          linarith
      _ = M + ε := by rw [div_mul_cancel₀ _ hT.ne']
  -- then on the closed cylinder, by continuity
  rintro ⟨x, t⟩ ⟨hx, ht⟩
  have hcl : (x, t) ∈ closure (closure Ω ×ˢ Ico 0 T) := by
    rw [closure_prod_eq, closure_closure, closure_Ico hT.ne]
    exact ⟨hx, ht⟩
  refine ContinuousWithinAt.closure_le hcl ?_ continuousWithinAt_const key
  exact (hu.continuousOn (x, t) ⟨hx, ht⟩).mono (prod_mono_right Ico_subset_Icc_self)

/-- **The parabolic maximum principle.** Let $\Omega \subseteq E$ be open, bounded and nonempty, and
let $\nu > 0$ and $T > 0$. Let $u$ be a classical subsolution of
$\partial_t u - \nu \Delta u \le 0$ on $\Omega \times (0, T)$. Then $u$ attains its maximum over
$\overline{\Omega} \times [0, T]$ at a point of the parabolic boundary $P = (\overline{\Omega}
\times \{0\}) \cup (\partial \Omega \times [0, T])$, that is,
$$\max_{\overline{\Omega} \times [0, T]} u = \max_P u.$$
This is Theorem 10.6 of [brezis2011functional].

The hypothesis that $\Omega$ is nonempty makes the maximum exist. The proof combines the
compactness of $P$ with `Heat.IsClassicalSubsolution.le_of_le_on_parabolicBoundary`. -/
theorem IsClassicalSubsolution.exists_isMaxOn_parabolicBoundary (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) (hν : 0 < ν) (hT : 0 < T)
    (hu : IsClassicalSubsolution ν Ω T u) :
    ∃ p ∈ parabolicBoundary Ω T, IsMaxOn u (closure Ω ×ˢ Icc 0 T) p := by
  obtain ⟨x, hx⟩ := hne
  have hPne : (parabolicBoundary Ω T).Nonempty := ⟨(x, 0), Or.inl ⟨subset_closure hx, rfl⟩⟩
  obtain ⟨p, hp, hpmax⟩ := (isCompact_parabolicBoundary hb T).exists_isMaxOn hPne
    (hu.continuousOn.mono (parabolicBoundary_subset hT.le))
  exact ⟨p, hp, fun q hq =>
    hu.le_of_le_on_parabolicBoundary hΩ hb hν hT (fun r hr => hpmax hr) q hq⟩

/-- **The maximum principle in the form of the numerical texts.** Let $\Omega \subseteq E$ be open
and bounded, and let $\nu > 0$ and $T > 0$. Let $u$ be a classical solution of
$\partial_t u = \nu \Delta u$ on $\Omega \times (0, T)$ with $u(x, t) = 0$ for
$x \in \partial \Omega$ and $t \in [0, T]$. If $M \in \mathbb{R}$ and $|u(y, 0)| \le M$ for all
$y \in \overline{\Omega}$, then
$$|u(x, t)| \le M \quad \text{for all } x \in \overline{\Omega},\ t \in [0, T].$$

This is the bound $\max_x |u(x, t)| \le \max_x |u_0(x)|$. The proof applies Theorem 10.6 of
[brezis2011functional] to $u$ and to $-u$. -/
theorem IsClassicalSolution.abs_le_of_eq_zero_frontier (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hν : 0 < ν) (hT : 0 < T) (hu : IsClassicalSolution ν Ω T u)
    (hΓ : ∀ x ∈ frontier Ω, ∀ t ∈ Icc 0 T, u (x, t) = 0) {M : ℝ}
    (hM : ∀ y ∈ closure Ω, |u (y, 0)| ≤ M) :
    ∀ x ∈ closure Ω, ∀ t ∈ Icc 0 T, |u (x, t)| ≤ M := by
  have hP : ∀ p ∈ parabolicBoundary Ω T, u p ≤ M ∧ -u p ≤ M := by
    rintro ⟨y, t⟩ (⟨hy, ht⟩ | ⟨hy, ht⟩)
    · simp only [mem_singleton_iff] at ht
      subst ht
      exact ⟨(le_abs_self _).trans (hM y hy), (neg_le_abs _).trans (hM y hy)⟩
    · have h0 : 0 ≤ M := (abs_nonneg _).trans (hM y (frontier_subset_closure hy))
      rw [hΓ y hy t ht]
      simp only [neg_zero]
      exact ⟨h0, h0⟩
  intro x hx t ht
  refine abs_le.2 ⟨?_, ?_⟩
  · have := hu.neg.isClassicalSubsolution.le_of_le_on_parabolicBoundary hΩ hb hν hT
      (fun p hp => (hP p hp).2) (x, t) ⟨hx, ht⟩
    simpa only [Pi.neg_apply, neg_le] using this
  · exact hu.isClassicalSubsolution.le_of_le_on_parabolicBoundary hΩ hb hν hT
      (fun p hp => (hP p hp).1) (x, t) ⟨hx, ht⟩


/-! ### The compatibility conditions are necessary (Remark 4) -/

variable {ν T : ℝ} {Ω : Set E} {u : E × ℝ → ℝ}

open scoped ContDiff in
/-- **The iterated heat equation.** Let $\Omega \subseteq E$ be open, and let $u$ be a classical
solution of $\partial_t u = \nu \Delta u$ on $\Omega \times (0, T)$ that is $C^\infty$ on
$E \times \mathbb{R}$. Then for every $j \in \mathbb{N}$,
$$\partial_t^j u = \nu^j \Delta_x^j u \quad \text{on } \Omega \times (0, T).$$

Here `Heat.timeDeriv` and `Heat.spaceLaplacian` are $\partial_t$ and $\Delta_x$. The proof is by
induction on $j$. It uses the commutation $\partial_t \Delta_x^j = \Delta_x^j \partial_t$ on
smooth functions (`Heat.timeDeriv_spaceLaplacian_iterate`) and the locality of both operators on
the open cylinder. -/
theorem IsClassicalSolution.timeDeriv_iterate_eqOn (hΩ : IsOpen Ω)
    (hu : IsClassicalSolution ν Ω T u) (hsmooth : ContDiff ℝ ∞ u) (j : ℕ) :
    EqOn (timeDeriv^[j] u) (ν ^ j • spaceLaplacian^[j] u) (Ω ×ˢ Ioo 0 T) := by
  have hV : IsOpen (Ω ×ˢ Ioo 0 T) := hΩ.prod isOpen_Ioo
  have heq : EqOn (timeDeriv u) (ν • spaceLaplacian u) (Ω ×ˢ Ioo 0 T) := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    exact hu.deriv_eq_laplacian x hx t ht
  induction j with
  | zero => intro p _; simp
  | succ j ih =>
    intro p hp
    rw [Function.iterate_succ_apply', timeDeriv_eqOn hV ih hp, timeDeriv_const_smul,
      timeDeriv_spaceLaplacian_iterate hsmooth, Pi.smul_apply,
      spaceLaplacian_iterate_eqOn hV heq j hp,
      spaceLaplacian_iterate_const_smul ν (contDiff_spaceLaplacian hsmooth) j,
      Function.iterate_succ_apply, pow_succ]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

open scoped ContDiff in
/-- **The compatibility conditions are necessary.** Let $\Omega \subseteq E$ be open, let
$\nu \neq 0$ and $T > 0$, and let $u$ be a classical solution of $\partial_t u = \nu \Delta u$
on $\Omega \times (0, T)$ that is $C^\infty$ on $E \times \mathbb{R}$ and satisfies
$u(x, t) = 0$ for $x \in \partial \Omega$ and $t \in (0, T)$. Then for every $j \in \mathbb{N}$
the initial datum $u_0 = u(\cdot, 0)$ satisfies
$$\Delta^j u_0 = 0 \quad \text{on } \partial \Omega.$$
These are the compatibility conditions (8) of Theorem 10.2(c) of [brezis2011functional], and the
statement is Remark 4 of chapter 10 of [brezis2011functional].

The source states the remark for $u \in C^\infty(\overline{\Omega} \times [0, \infty))$ in the
sense of its footnote 16. There $u(\cdot, 0)$ is only known to be continuous on
$\overline{\Omega}$, and $\Delta^j u_0$ on the boundary means the continuous extension of
$\Delta^j u$. The smoothness of $u$ on all of $E \times \mathbb{R}$ assumed here makes the
statement meaningful as written. It is the smoothness that the solutions of Theorem 10.2(c) have
in the interior of their domain of smoothness.

The proof follows the source. By `Heat.IsClassicalSolution.timeDeriv_iterate_eqOn`,
$\partial_t^j u = \nu^j \Delta_x^j u$ on $\Omega \times (0, T)$. Since $u$ vanishes on
$\partial \Omega \times (0, T)$, also $\partial_t^j u = 0$ there
(`Heat.iterate_deriv_eq_zero_of_eqOn`). Both sides are continuous on $E \times \mathbb{R}$, so
the identities pass to $\overline{\Omega} \times [0, T]$ and $\partial \Omega \times [0, T]$.
Comparing them at $(x, 0)$ for $x \in \partial \Omega$ gives $\nu^j \Delta^j u_0(x) = 0$. -/
theorem IsClassicalSolution.iteratedLaplacian_eq_zero_frontier (hΩ : IsOpen Ω) (hν : ν ≠ 0)
    (hT : 0 < T) (hu : IsClassicalSolution ν Ω T u) (hsmooth : ContDiff ℝ ∞ u)
    (hΓ : ∀ x ∈ frontier Ω, ∀ t ∈ Ioo 0 T, u (x, t) = 0) (j : ℕ) :
    ∀ x ∈ frontier Ω, (Laplacian.laplacian^[j] fun y ↦ u (y, 0)) x = 0 := by
  intro x hx
  -- `∂ₜ^j u = ν^j Δ_x^j u` on the closed cylinder, by continuity
  have hcl : EqOn (timeDeriv^[j] u) (ν ^ j • spaceLaplacian^[j] u) (closure Ω ×ˢ Icc 0 T) := by
    have h := hu.timeDeriv_iterate_eqOn hΩ hsmooth j
    refine h.of_subset_closure (contDiff_timeDeriv_iterate hsmooth j).continuous.continuousOn
      ((contDiff_spaceLaplacian_iterate hsmooth j).continuous.const_smul _).continuousOn
      (prod_mono subset_closure Ioo_subset_Icc_self) ?_
    rw [closure_prod_eq, closure_Ioo hT.ne]
  -- `∂ₜ^j u (x, 0) = 0`, by continuity from the lateral boundary
  have hzero : timeDeriv^[j] u (x, 0) = 0 :=
    timeDeriv_iterate_apply_zero_eq_zero hT hsmooth (hΓ x hx) j
  have h3 := hcl (x := (x, 0)) ⟨frontier_subset_closure hx, left_mem_Icc.2 hT.le⟩
  rw [hzero, Pi.smul_apply, smul_eq_mul, eq_comm, mul_eq_zero,
    or_iff_right (pow_ne_zero j hν)] at h3
  rw [← spaceLaplacian_iterate_slice]
  exact h3

end Heat
