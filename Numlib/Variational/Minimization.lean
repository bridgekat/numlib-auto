/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Existence of minimizers of a functional on a closed set

A functional $f : V \to \mathbb{R}$ is **coercive** on a set $K$ if $f(x) \to \infty$ as
$\|x\| \to \infty$ in $K$. This module proves the finite-dimensional existence theorem of
[han2009theoretical], Theorem 3.3.13: a lower semicontinuous functional on a nonempty closed subset
$K$ of a finite-dimensional subspace attains its infimum on $K$ if $K$ is bounded or $f$ is coercive
on $K$. Neither the set nor the functional needs to be convex. Convexity enters only in uniqueness:
a strictly convex functional has at most one minimizer. The module also shows that a strongly convex
functional with a local lower bound is coercive, so that on a finite-dimensional space a lower
semicontinuous strongly convex functional has exactly one minimizer on a nonempty closed set.

## Main definitions

* `IsCoerciveFunctionalOn`: $f$ is coercive on $K$.

## Main results

* `isCoerciveFunctionalOn_of_rpow_sub_mul_le`: a functional with $f(x) \ge c\|x\|^r - C\|x\|$,
  $c > 0$, $r > 1$, is coercive.
* `exists_isMinOn_of_isClosed_of_finiteDimensional`,
  `exists_isMinOn_of_isBounded_of_finiteDimensional`: a lower semicontinuous functional on a
  nonempty closed subset of a finite-dimensional subspace attains its minimum if it is coercive or
  the set is bounded.
* `IsMinOn.eq_of_strictConvexOn`: a strictly convex functional has at most one minimizer on a set.
* `StrongConvexOn.isCoerciveFunctionalOn`, `StrongConvexOn.isCoerciveFunctionalOn_of_continuous`: a
  strongly convex functional that is bounded below near one point, for example a continuous one, is
  coercive.
* `existsUnique_isMinOn_of_strongConvexOn`: on a finite-dimensional space, a lower semicontinuous
  strongly convex functional has exactly one minimizer on a nonempty closed set.

## Implementation notes

* The infinite-dimensional theorems of the same section of [han2009theoretical], on closed convex
  sets of a reflexive space, are in `Numlib.Variational.WeakMinimization`. They rest on the weak
  sequential compactness of bounded sets, which that module states as the class
  `WeaklySeqCompactSpace`. Reflexivity is `NormedSpace.IsReflexive` of
  `Numlib.Analysis.Normed.Module.Reflexive`, and the instance `WeaklySeqCompactSpace.of_isReflexive`
  derives the class from it. Mathlib's `Module.IsReflexive` is the algebraic double dual, which is a
  different condition.
* `StrongConvexOn K m f` is Mathlib's `UniformConvexOn K (fun ρ => m / 2 * ρ ^ 2) f`. A modulus
  $\rho \|x - y\|^2$ in the literature is $m = 2\rho$ here.
-/

open Bornology

section Coercive

variable {V : Type*} [SeminormedAddCommGroup V]

/-- A functional $f : V \to \mathbb{R}$ is **coercive on a set** $K$ if for every $M \in \mathbb{R}$
there is $R \in \mathbb{R}$ with $f(x) \ge M$ for all $x \in K$ with $\|x\| \ge R$. So
$f(x) \to +\infty$ as $\|x\| \to \infty$ in $K$. This is Definition 3.3.9 of
[han2009theoretical].

This is a condition on a functional. It is different from the coercivity of an operator or of a
sesquilinear form, $\operatorname{Re} \langle Ax, x \rangle \ge c \|x\|^2$, which is a lower
bound of quadratic order and not a growth condition. -/
def IsCoerciveFunctionalOn (f : V → ℝ) (K : Set V) : Prop :=
  ∀ M : ℝ, ∃ R : ℝ, ∀ x ∈ K, R ≤ ‖x‖ → M ≤ f x

/-- Every functional is coercive on a bounded set $K$: take $R$ larger than the bound of $K$. -/
theorem IsCoerciveFunctionalOn.of_isBounded {f : V → ℝ} {K : Set V} (hK : IsBounded K) :
    IsCoerciveFunctionalOn f K := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hK
  exact fun M => ⟨C + 1, fun x hx hx' => absurd (hC x hx) (by linarith)⟩

/-- If $f$ is coercive on $K$ and $K' \subseteq K$, then $f$ is coercive on $K'$. -/
theorem IsCoerciveFunctionalOn.mono {f : V → ℝ} {K K' : Set V} (h : IsCoerciveFunctionalOn f K)
    (hKK : K' ⊆ K) : IsCoerciveFunctionalOn f K' :=
  fun M => (h M).imp fun _ hR x hx => hR x (hKK hx)

/-- **A power lower bound gives coercivity.** Let $c > 0$, $r > 1$ and $C \in \mathbb{R}$. If
$$f(x) \ge c \|x\|^r - C \|x\| \quad \text{for all } x \in K,$$
then $f$ is coercive on $K$ in the sense of Definition 3.3.9 of [han2009theoretical]. -/
theorem isCoerciveFunctionalOn_of_rpow_sub_mul_le {f : V → ℝ} {K : Set V} {c C r : ℝ}
    (hc : 0 < c) (hr : 1 < r)
    (hf : ∀ x ∈ K, c * ‖x‖ ^ r - C * ‖x‖ ≤ f x) : IsCoerciveFunctionalOn f K := by
  intro M
  have hr1 : 0 < r - 1 := by linarith
  refine ⟨max 1 (max M ((max (C + 1) 0 / c) ^ (1 / (r - 1)))), fun x hx hxR ↦ ?_⟩
  have h1 : 1 ≤ ‖x‖ := (le_max_left _ _).trans hxR
  have hM : M ≤ ‖x‖ := ((le_max_left _ _).trans (le_max_right _ _)).trans hxR
  have hA : (max (C + 1) 0 / c) ^ (1 / (r - 1)) ≤ ‖x‖ :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hxR
  -- `c ‖x‖^{r−1} ≥ C + 1`
  have hpow : max (C + 1) 0 / c ≤ ‖x‖ ^ (r - 1) := by
    have := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _) hA hr1.le
    rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel hr1.ne', Real.rpow_one] at this
  have hkey : C + 1 ≤ c * ‖x‖ ^ (r - 1) := by
    rw [div_le_iff₀ hc] at hpow
    linarith [le_max_left (C + 1) 0]
  have hsplit : ‖x‖ ^ r = ‖x‖ ^ (r - 1) * ‖x‖ := by
    rw [← Real.rpow_add_one (by positivity : ‖x‖ ≠ 0)]
    ring_nf
  calc M ≤ ‖x‖ := hM
    _ ≤ (c * ‖x‖ ^ (r - 1) - C) * ‖x‖ := by nlinarith
    _ = c * ‖x‖ ^ r - C * ‖x‖ := by rw [hsplit]; ring
    _ ≤ f x := hf x hx

end Coercive

section Existence

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable [LocallyCompactSpace 𝕜]

/-- Let $\mathbb{K}$ be a locally compact nontrivially normed field, $V$ a normed space over
$\mathbb{K}$, and $S$ a finite-dimensional subspace of $V$. A closed bounded set $K \subseteq S$
is compact, because a finite-dimensional normed space is a proper metric space. -/
theorem isCompact_of_isBounded_of_subset_finiteDimensional {K : Set V} (S : Submodule 𝕜 V)
    [FiniteDimensional 𝕜 S] (hKS : K ⊆ S) (hcl : IsClosed K) (hbd : IsBounded K) :
    IsCompact K := by
  have : ProperSpace S := FiniteDimensional.proper 𝕜 S
  have hpre : IsCompact (Subtype.val ⁻¹' K : Set S) := by
    refine Metric.isCompact_of_isClosed_isBounded (hcl.preimage continuous_subtype_val) ?_
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hbd
    refine (Metric.isBounded_closedBall (x := (0 : S)) (r := C)).subset fun w hw => ?_
    simpa [Metric.mem_closedBall, dist_zero_right] using hC _ hw
  have himg : K = Subtype.val '' (Subtype.val ⁻¹' K : Set S) := by
    ext x
    exact ⟨fun hx => ⟨⟨x, hKS hx⟩, hx, rfl⟩, by rintro ⟨w, hw, rfl⟩; exact hw⟩
  rw [himg]
  exact hpre.image continuous_subtype_val

/-- **Existence of a minimizer.** Let $\mathbb{K}$ be a locally compact nontrivially normed field,
$V$ a normed space over $\mathbb{K}$, $S$ a finite-dimensional subspace of $V$, and
$K \subseteq S$ a nonempty set that is closed in $V$. Let $f : V \to \mathbb{R}$ be lower
semicontinuous on $K$ and coercive on $K$. Then $f$ attains its minimum on $K$: there is
$u \in K$ with $f(u) \le f(v)$ for all $v \in K$. This is Theorem 3.3.13 of
[han2009theoretical], with the case of a bounded $K$ in
`exists_isMinOn_of_isBounded_of_finiteDimensional`.

Coercivity reduces the problem to a sublevel set, which is closed by lower semicontinuity and
bounded by coercivity, hence compact. A bounded $K$ makes $f$ coercive on $K$
(`IsCoerciveFunctionalOn.of_isBounded`), so the bounded case follows from the coercive one. The
source assumes $K$ and $f$ convex; convexity is used only for uniqueness, in
`IsMinOn.eq_of_strictConvexOn`. -/
theorem exists_isMinOn_of_isClosed_of_finiteDimensional {K : Set V} (S : Submodule 𝕜 V)
    [FiniteDimensional 𝕜 S] (hKS : K ⊆ S) (hcl : IsClosed K) (hne : K.Nonempty) {f : V → ℝ}
    (hlsc : LowerSemicontinuousOn f K) (hf : IsCoerciveFunctionalOn f K) :
    ∃ u ∈ K, IsMinOn f K u := by
  obtain ⟨v₀, hv₀⟩ := hne
  obtain ⟨R, hR⟩ := hf (f v₀ + 1)
  set R' := max R ‖v₀‖ with hR'
  set K' := K ∩ Metric.closedBall (0 : V) R' with hK'
  have hsub : K' ⊆ K := Set.inter_subset_left
  have hv₀' : v₀ ∈ K' := ⟨hv₀, by simp [Metric.mem_closedBall, dist_zero_right, hR']⟩
  have hcpt : IsCompact K' :=
    isCompact_of_isBounded_of_subset_finiteDimensional S (hsub.trans hKS)
      (hcl.inter Metric.isClosed_closedBall)
      (Metric.isBounded_closedBall.subset Set.inter_subset_right)
  obtain ⟨a, haK', hamin⟩ := (hlsc.mono hsub).exists_isMinOn ⟨v₀, hv₀'⟩ hcpt
  refine ⟨a, hsub haK', isMinOn_iff.2 fun v hv => ?_⟩
  by_cases hvb : v ∈ Metric.closedBall (0 : V) R'
  · exact isMinOn_iff.1 hamin v ⟨hv, hvb⟩
  · have hnorm : R ≤ ‖v‖ := by
      simp only [Metric.mem_closedBall, dist_zero_right, not_le, hR'] at hvb
      exact (le_max_left R ‖v₀‖).trans hvb.le
    have h1 : f v₀ + 1 ≤ f v := hR v hv hnorm
    have h2 : f a ≤ f v₀ := isMinOn_iff.1 hamin v₀ hv₀'
    linarith

/-- **Existence of a minimizer on a bounded set.** Let $\mathbb{K}$ be a locally compact
nontrivially normed field, $V$ a normed space over $\mathbb{K}$, $S$ a finite-dimensional
subspace of $V$, and $K \subseteq S$ nonempty, closed and bounded. If $f : V \to \mathbb{R}$ is
lower semicontinuous on $K$, then $f$ attains its minimum on $K$. This is Theorem 3.3.13 of
[han2009theoretical], for a bounded set.

This is the bounded case of `exists_isMinOn_of_isClosed_of_finiteDimensional`. -/
theorem exists_isMinOn_of_isBounded_of_finiteDimensional {K : Set V} (S : Submodule 𝕜 V)
    [FiniteDimensional 𝕜 S] (hKS : K ⊆ S) (hcl : IsClosed K) (hbd : IsBounded K)
    (hne : K.Nonempty) {f : V → ℝ} (hlsc : LowerSemicontinuousOn f K) :
    ∃ u ∈ K, IsMinOn f K u :=
  exists_isMinOn_of_isClosed_of_finiteDimensional S hKS hcl hne hlsc
    (IsCoerciveFunctionalOn.of_isBounded hbd)

end Existence

section Uniqueness

variable {V : Type*} [AddCommMonoid V] [Module ℝ V]

/-- **Uniqueness of a minimizer.** Let $V$ be a real vector space, $K \subseteq V$, and
$f : V \to \mathbb{R}$ strictly convex on $K$. If $u_1, u_2 \in K$ both minimize $f$ over $K$,
then $u_1 = u_2$. This is the uniqueness clause of Theorems 3.3.12 and 3.3.13 of
[han2009theoretical].

This is Mathlib's `StrictConvexOn.eq_of_isMinOn` under the name of this module, so that the
module states the whole theorem. -/
theorem IsMinOn.eq_of_strictConvexOn {f : V → ℝ} {K : Set V} (hf : StrictConvexOn ℝ K f)
    {u₁ u₂ : V} (h₁ : IsMinOn f K u₁) (h₂ : IsMinOn f K u₂) (hu₁ : u₁ ∈ K) (hu₂ : u₂ ∈ K) :
    u₁ = u₂ :=
  StrictConvexOn.eq_of_isMinOn hf h₁ h₂ hu₁ hu₂

end Uniqueness

section StrongConvex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **A strongly convex functional is coercive.** Let $V$ be a real normed space, $K \subseteq V$,
and let $f : V \to \mathbb{R}$ be $m$-strongly convex on $K$ with $m > 0$. If $f$ is bounded
below on $K \cap B(x_0, r)$ for one point $x_0 \in K$ and one radius $r > 0$, then $f$ is
coercive on $K$.

Strong convexity alone does not give coercivity. A discontinuous linear functional $\ell$ on an
infinite-dimensional Hilbert space is convex, so $x \mapsto \ell(x) + \|x\|^2$ is strongly
convex, but it tends to $-\infty$ along a suitable sequence and is unbounded below on every
ball. So a local lower bound is a hypothesis. Lower semicontinuity at a point of $K$ gives one,
and `existsUnique_isMinOn_of_strongConvexOn` uses this.

The proof interpolates. For $y \in K$ far from $x_0$, the point $z = (1 - t)x_0 + ty$ with
$t = r / (2\|y - x_0\|)$ lies in $K \cap B(x_0, r)$, and the strong convexity inequality at $z$
gives a lower bound for $f(y)$ of the form $\tfrac{m}{4}\|y - x_0\|^2 - A\|y - x_0\|$, with
$A = 2(|b| + |f(x_0)|)/r$ for the lower bound $b$ of $f$ on $K \cap B(x_0, r)$. The quadratic
term dominates the linear one. -/
theorem StrongConvexOn.isCoerciveFunctionalOn {K : Set V} {f : V → ℝ} {m : ℝ}
    (hf : StrongConvexOn K m f) (hm : 0 < m) {x₀ : V} (hx₀ : x₀ ∈ K) {r : ℝ} (hr : 0 < r)
    (hbdd : BddBelow (f '' (K ∩ Metric.ball x₀ r))) : IsCoerciveFunctionalOn f K := by
  obtain ⟨c, hc⟩ := hbdd
  set A : ℝ := 2 * (|c| + |f x₀|) / r with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  intro M
  refine ⟨‖x₀‖ + max r (4 / m * (A + |M| + 1) + 1), fun y hy hynorm => ?_⟩
  set s : ℝ := ‖y - x₀‖ with hsdef
  have hsge : max r (4 / m * (A + |M| + 1) + 1) ≤ s := by
    have h1 : ‖y‖ - ‖x₀‖ ≤ s := by rw [hsdef]; exact norm_sub_norm_le y x₀
    linarith
  have hsr : r ≤ s := (le_max_left _ _).trans hsge
  have hs1 : 4 / m * (A + |M| + 1) + 1 ≤ s := (le_max_right _ _).trans hsge
  have hspos : 0 < s := lt_of_lt_of_le hr hsr
  set t : ℝ := r / (2 * s) with htdef
  have htpos : 0 < t := by rw [htdef]; exact div_pos hr (by linarith)
  have hthalf : t ≤ 1 / 2 := by
    rw [htdef, div_le_iff₀ (by linarith)]; linarith
  have ht1 : 0 ≤ 1 - t := by linarith
  have hts : t * s = r / 2 := by rw [htdef]; field_simp
  have hzK : (1 - t) • x₀ + t • y ∈ K := hf.1 hx₀ hy ht1 htpos.le (by ring)
  have hzball : (1 - t) • x₀ + t • y ∈ Metric.ball x₀ r := by
    have hrw : (1 - t) • x₀ + t • y - x₀ = t • (y - x₀) := by module
    rw [Metric.mem_ball, dist_eq_norm, hrw, norm_smul, Real.norm_eq_abs, abs_of_pos htpos,
      ← hsdef, hts]
    linarith
  have hcz : c ≤ f ((1 - t) • x₀ + t • y) := hc ⟨_, ⟨hzK, hzball⟩, rfl⟩
  have hsc := hf.2 hx₀ hy ht1 htpos.le (by ring : 1 - t + t = 1)
  simp only [smul_eq_mul] at hsc
  rw [norm_sub_rev, ← hsdef] at hsc
  have hfx₀ : (1 - t) * f x₀ ≤ |f x₀| :=
    calc (1 - t) * f x₀ ≤ (1 - t) * |f x₀| := mul_le_mul_of_nonneg_left (le_abs_self _) ht1
      _ ≤ 1 * |f x₀| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ = |f x₀| := one_mul _
  have key : c - |f x₀| + m / 4 * (t * s ^ 2) ≤ t * f y := by
    have h2 : m / 4 * (t * s ^ 2) ≤ (1 - t) * t * (m / 2 * s ^ 2) := by
      nlinarith [mul_nonneg (mul_nonneg (mul_nonneg htpos.le (sq_nonneg s)) hm.le)
        (by linarith : (0 : ℝ) ≤ 1 - 2 * t)]
    linarith
  have hAts : A * (t * s) = |c| + |f x₀| := by rw [hts, hA]; field_simp
  have hfy : m / 4 * s ^ 2 - A * s ≤ f y := by
    refine le_of_mul_le_mul_left ?_ htpos
    have hrw : t * (m / 4 * s ^ 2 - A * s) = m / 4 * (t * s ^ 2) - A * (t * s) := by ring
    rw [hrw, hAts]
    linarith [neg_abs_le c]
  have hs1' : (1 : ℝ) ≤ s := by
    have : 0 ≤ 4 / m * (A + |M| + 1) := by positivity
    linarith
  have hlin : |M| + 1 ≤ m / 4 * s - A := by
    have hmul : m / 4 * (4 / m * (A + |M| + 1) + 1) ≤ m / 4 * s :=
      mul_le_mul_of_nonneg_left hs1 (by positivity)
    have hid : m / 4 * (4 / m * (A + |M| + 1) + 1) = A + |M| + 1 + m / 4 := by field_simp
    rw [hid] at hmul
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hlin hspos.le, le_abs_self M, abs_nonneg M]

/-- If $f$ is $m$-strongly convex on all of $V$ and $K \subseteq V$ is convex, then $f$ is
$m$-strongly convex on $K$. -/
theorem StrongConvexOn.mono_of_univ {K : Set V} {f : V → ℝ} {m : ℝ}
    (hf : StrongConvexOn Set.univ m f) (hK : Convex ℝ K) : StrongConvexOn K m f :=
  ⟨hK, fun x _ y _ _ _ hs ht hst ↦ hf.2 (Set.mem_univ x) (Set.mem_univ y) hs ht hst⟩

/-- Let $V$ be a real normed space, let $K \subseteq V$ be nonempty, and let $f : V \to \mathbb{R}$
be continuous and $m$-strongly convex on $K$ with $m > 0$. Then $f$ is coercive on $K$.

Continuity at a point of $K$ gives the local lower bound that
`StrongConvexOn.isCoerciveFunctionalOn` needs. -/
theorem StrongConvexOn.isCoerciveFunctionalOn_of_continuous {K : Set V} {f : V → ℝ} {m : ℝ}
    (hf : StrongConvexOn K m f) (hm : 0 < m) (hne : K.Nonempty) (hc : Continuous f) :
    IsCoerciveFunctionalOn f K := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, ∀ x ∈ Metric.ball x₀ r, f x₀ - 1 < f x := by
    have h := (hc.tendsto x₀).eventually (lt_mem_nhds (show f x₀ - 1 < f x₀ by linarith))
    rw [Metric.eventually_nhds_iff_ball] at h
    exact h
  refine hf.isCoerciveFunctionalOn hm hx₀ hr ⟨f x₀ - 1, ?_⟩
  rintro _ ⟨x, ⟨-, hxb⟩, rfl⟩
  exact (hball x hxb).le

variable [FiniteDimensional ℝ V]

/-- **Existence and uniqueness of the minimizer of a strongly convex functional.** Let $V$ be a
finite-dimensional real normed space, let $K \subseteq V$ be nonempty and closed, and let
$f : V \to \mathbb{R}$ be lower semicontinuous on $K$ and $m$-strongly convex on $K$ with
$m > 0$. Then $f$ has exactly one minimizer over $K$.

Convexity of $K$ is part of `StrongConvexOn K m f`. Lower semicontinuity cannot be omitted,
although textbook statements often omit it: on $K = [0, 1]$, the function with
$f(x) = (x - 1)^2$ for $x < 1$ and $f(1) = 5$ is strongly convex on $K$ and has no minimizer
there. Existence is `exists_isMinOn_of_isClosed_of_finiteDimensional` with coercivity from
`StrongConvexOn.isCoerciveFunctionalOn`, whose local lower bound comes from lower semicontinuity
at a point of $K$. Uniqueness is `IsMinOn.eq_of_strictConvexOn` applied to
`StrongConvexOn.strictConvexOn`. -/
theorem existsUnique_isMinOn_of_strongConvexOn {K : Set V} (hcl : IsClosed K) (hne : K.Nonempty)
    {f : V → ℝ} {m : ℝ} (hm : 0 < m) (hf : StrongConvexOn K m f)
    (hlsc : LowerSemicontinuousOn f K) : ∃! u, u ∈ K ∧ IsMinOn f K u := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, ∀ x ∈ Metric.ball x₀ r, x ∈ K → f x₀ - 1 < f x := by
    have h := hlsc x₀ hx₀ (f x₀ - 1) (by linarith)
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff_ball] at h
    exact h
  have hbdd : BddBelow (f '' (K ∩ Metric.ball x₀ r)) := by
    refine ⟨f x₀ - 1, ?_⟩
    rintro _ ⟨x, ⟨hxK, hxb⟩, rfl⟩
    exact (hball x hxb hxK).le
  obtain ⟨u, huK, humin⟩ :=
    exists_isMinOn_of_isClosed_of_finiteDimensional (𝕜 := ℝ) (⊤ : Submodule ℝ V) (by simp) hcl
      ⟨x₀, hx₀⟩ hlsc (hf.isCoerciveFunctionalOn hm hx₀ hr hbdd)
  refine ⟨u, ⟨huK, humin⟩, ?_⟩
  rintro v ⟨hvK, hvmin⟩
  exact IsMinOn.eq_of_strictConvexOn (hf.strictConvexOn hm) hvmin humin hvK huK

end StrongConvex
