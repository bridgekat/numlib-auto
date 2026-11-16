/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Subdifferential.Defs
import Numlib.Analysis.Convex.Duality.InnerPairing
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Filter.Prod
import Mathlib.Tactic.Ring

/-!
# Clarke directional derivatives and subgradients

Let $E$ be a real inner product space and let $f : E \to \mathbb{R}$. The **Clarke directional
derivative** of $f$ at $x$ in the direction $d$ is the upper limit
$$f^\circ(x; d) = \limsup_{y \to x,\ t \downarrow 0} \frac{f(y + t d) - f(y)}{t},$$
and the **Clarke subdifferential** is the set $\partial f(x) = \{g \in E \mid \langle g, d \rangle
\le f^\circ(x; d) \text{ for all } d\}$. These are the generalized derivatives of Section 3.1.4 of
[conn2000trust]. This file proves the basic properties of $f^\circ(x; \cdot)$ for a function $f$
that is Lipschitz near $x$: it is bounded by the Lipschitz constant, subadditive, positively
homogeneous and Lipschitz in $d$, it is upper semicontinuous in $x$, and it equals $f'(x) d$ at a
point of strict differentiability. The subdifferential is closed and convex, compact in finite
dimension, and its support function is $f^\circ(x; \cdot)$, the representation (3.1.4) of
[conn2000trust].

## Main definitions

* `Optimization.clarkeDerivative`: the Clarke directional derivative $f^\circ(x; d)$.
* `Optimization.clarkeSubgradient`: the Clarke subdifferential $\partial f(x)$.
* `Optimization.HasClarkeSupport`: the support function of $\partial f(x)$ is $f^\circ(x; \cdot)$.

## Main results

* `Optimization.abs_clarkeDerivative_le`: if $f$ is $L$-Lipschitz near $x$, then
  $|f^\circ(x; d)| \le L \|d\|$.
* `Optimization.clarkeDerivative_add_le`, `Optimization.clarkeDerivative_pos_smul`:
  $f^\circ(x; \cdot)$ is subadditive and positively homogeneous.
* `Optimization.lipschitzWith_clarkeDerivative`: $f^\circ(x; \cdot)$ is $L$-Lipschitz.
* `Optimization.eventually_clarkeDerivative_le_of_lt`: $y \mapsto f^\circ(y; d)$ is upper
  semicontinuous at $x$.
* `Optimization.clarkeDerivative_eq_of_hasStrictFDerivAt`: at a point of strict differentiability,
  $f^\circ(x; d) = f'(x) d$.
* `Optimization.clarkeSubgradient_subset_subdifferential`: for a continuous convex $f$, every Clarke
  subgradient is a subgradient in the sense of convex analysis.
* `Optimization.isCompact_clarkeSubgradient`: in finite dimension, $\partial f(x)$ is compact.
* `Optimization.hasClarkeSupport_of_lipschitzOnWith`: in a Hilbert space, $\sup_{g \in \partial
  f(x)} \langle g, d \rangle = f^\circ(x; d)$ for every $d$.

## Implementation notes

* The upper limit is `Filter.limsup` in $\mathbb{R}$ along the product filter of $y \to x$ and
  $t \to 0^+$. A real upper limit has the intended value only when the quotients are eventually
  bounded. This holds when $f$ is Lipschitz near $x$, which most results assume. The results on
  constant functions, on strictly differentiable functions, and on the closedness and convexity of
  $\partial f(x)$ do not need it.
* "Lipschitz near $x$" is the pair of hypotheses `U ∈ 𝓝 x` and `LipschitzOnWith L f U`.
-/

open Filter Metric ConvexAnalysis
open scoped Topology RealInnerProductSpace NNReal

namespace Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private abbrev clarkeFilter (x : E) : Filter (E × ℝ) := 𝓝 x ×ˢ 𝓝[>] (0 : ℝ)

private noncomputable def clarkeQuotient (f : E → ℝ) (d : E) (p : E × ℝ) : ℝ :=
  (f (p.1 + p.2 • d) - f p.1) / p.2

/-- The **Clarke directional derivative** of $f : E \to \mathbb{R}$ at $x$ in the direction $d$:
$$f^\circ(x; d) = \limsup_{y \to x,\ t \downarrow 0} \frac{f(y + t d) - f(y)}{t}.$$
This is the generalized directional derivative of Section 3.1.4 of [conn2000trust].

The upper limit is `Filter.limsup` in $\mathbb{R}$ along the product of the neighborhood filter of
$x$ and the filter of right neighborhoods of $0$. It has the intended value when the quotients are
eventually bounded, for example when
$f$ is Lipschitz near $x$ (see `Optimization.abs_clarkeDerivative_le`). Otherwise the value of
the real `limsup` is not meaningful. -/
noncomputable def clarkeDerivative (f : E → ℝ) (x d : E) : ℝ :=
  limsup (clarkeQuotient f d) (clarkeFilter x)

private theorem tendsto_clarkeShift (x d : E) :
    Tendsto (fun p : E × ℝ ↦ (p.1 + p.2 • d, p.2)) (clarkeFilter x) (clarkeFilter x) := by
  have ht : Tendsto Prod.snd (clarkeFilter x) (𝓝[>] (0 : ℝ)) := tendsto_snd
  have ht₀ : Tendsto Prod.snd (clarkeFilter x) (𝓝 (0 : ℝ)) := ht.mono_right nhdsWithin_le_nhds
  have hs : Tendsto (fun p : E × ℝ ↦ p.2 • d) (clarkeFilter x) (𝓝 (0 : E)) := by
    simpa only [zero_smul] using ht₀.smul (tendsto_const_nhds (x := d))
  have hy : Tendsto Prod.fst (clarkeFilter x) (𝓝 x) := tendsto_fst
  have hh : Tendsto (fun p : E × ℝ ↦ p.1 + p.2 • d) (clarkeFilter x) (𝓝 x) := by
    simpa only [add_zero] using hy.add hs
  exact hh.prodMk ht

private theorem eventually_abs_clarkeQuotient_le {f : E → ℝ} {x : E} {U : Set E} {L : ℝ≥0}
    (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith L f U) (d : E) :
    ∀ᶠ p in clarkeFilter x, |clarkeQuotient f d p| ≤ (L : ℝ) * ‖d‖ := by
  let F := clarkeFilter x
  have hy : Tendsto Prod.fst F (𝓝 x) := tendsto_fst
  have ht : Tendsto Prod.snd F (𝓝[>] (0 : ℝ)) := tendsto_snd
  have hy' : Tendsto (fun p : E × ℝ ↦ p.1 + p.2 • d) F (𝓝 x) :=
    tendsto_fst.comp (tendsto_clarkeShift x d)
  filter_upwards [hy.eventually hU, hy'.eventually hU,
    ht.eventually (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] 0)] with p hp hp' htp
  change 0 < p.2 at htp
  have h := hL.dist_le_mul _ hp' _ hp
  rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_pos htp] at h
  change |(f (p.1 + p.2 • d) - f p.1) / p.2| ≤ (L : ℝ) * ‖d‖
  rw [abs_div, abs_of_pos htp]
  apply (div_le_iff₀ htp).2
  convert h using 1
  ring
/-- Let $f : E \to \mathbb{R}$ be $L$-Lipschitz on a neighborhood $U$ of $x$. Then for every
direction $d$,
$$|f^\circ(x; d)| \le L \|d\|.$$
In particular $f^\circ(x; d)$ is finite. This bound is used in Section 3.1.4 of [conn2000trust]. -/
theorem abs_clarkeDerivative_le {f : E → ℝ} {x : E} {U : Set E} {L : ℝ≥0}
    (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith L f U) (d : E) :
    |clarkeDerivative f x d| ≤ (L : ℝ) * ‖d‖ := by
  let F := clarkeFilter x
  let q := clarkeQuotient f d
  have habs := eventually_abs_clarkeQuotient_le hU hL d
  have hlow := habs.mono fun _ hp ↦ (abs_le.mp hp).1
  have hupp := habs.mono fun _ hp ↦ (abs_le.mp hp).2
  have hb : F.IsBoundedUnder (· ≤ ·) q := ⟨_, hupp⟩
  have ha : F.IsBoundedUnder (· ≥ ·) q := ⟨_, hlow⟩
  change |limsup q F| ≤ (L : ℝ) * ‖d‖
  refine abs_le.mpr ⟨le_limsup_of_le hb (fun a ha' ↦ ?_),
    limsup_le_of_le ha.isCoboundedUnder_le hupp⟩
  obtain ⟨p, hp, hp'⟩ := (hlow.and ha').exists
  exact hp.trans hp'

/-- Let $f : E \to \mathbb{R}$ be $L$-Lipschitz on a neighborhood $U$ of $x$, and let
$y : (0, \infty) \to E$ be a path with $y(t) \to x$ as $t \to 0^+$. If
$$a \le \frac{f(y(t) + t d) - f(y(t))}{t}$$
for all sufficiently small $t > 0$, then $a \le f^\circ(x; d)$. -/
theorem le_clarkeDerivative_of_eventually_path_quotient_ge
    {f : E → ℝ} {x d : E} {U : Set E} {L : ℝ≥0} {a : ℝ} {y : ℝ → E}
    (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith L f U)
    (hy : Tendsto y (𝓝[>] (0 : ℝ)) (𝓝 x))
    (ha : ∀ᶠ t in 𝓝[>] (0 : ℝ), a ≤ (f (y t + t • d) - f (y t)) / t) :
    a ≤ clarkeDerivative f x d := by
  have ht : Tendsto (fun t : ℝ => (y t, t)) (𝓝[>] (0 : ℝ)) (clarkeFilter x) :=
    hy.prodMk tendsto_id
  have hF : ∃ᶠ p in clarkeFilter x, a ≤ clarkeQuotient f d p :=
    ht.frequently ha.frequently
  exact le_limsup_of_frequently_le hF
    ⟨_, (eventually_abs_clarkeQuotient_le hU hL d).mono fun _ hp => (abs_le.1 hp).2⟩

/-- Let $f : E \to \mathbb{R}$ be $L$-Lipschitz on a neighborhood $U$ of $x$. If
$$a \le \frac{f(x + t d) - f(x)}{t}$$
for all sufficiently small $t > 0$, then $a \le f^\circ(x; d)$.

This is the case of the constant path $y(t) = x$ in
`Optimization.le_clarkeDerivative_of_eventually_path_quotient_ge`. -/
theorem le_clarkeDerivative_of_eventually_base_quotient_ge
    {f : E → ℝ} {x d : E} {U : Set E} {L : ℝ≥0} {a : ℝ}
    (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith L f U)
    (ha : ∀ᶠ t in 𝓝[>] (0 : ℝ), a ≤ (f (x + t • d) - f x) / t) :
    a ≤ clarkeDerivative f x d :=
  le_clarkeDerivative_of_eventually_path_quotient_ge hU hL tendsto_const_nhds ha

/-- Let $f : E \to \mathbb{R}$ be $L$-Lipschitz on a neighborhood $U$ of $x$. If
$f^\circ(x; d) < b$, then
$$\frac{f(x + t d) - f(x)}{t} < b$$
for all sufficiently small $t > 0$.

This step is used in the proof of Theorem 3.2.15 of [conn2000trust]. -/
theorem eventually_base_quotient_lt_of_clarkeDerivative_lt
    {f : E → ℝ} {x d : E} {U : Set E} {L : ℝ≥0} {b : ℝ}
    (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith L f U) (hb : clarkeDerivative f x d < b) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), (f (x + t • d) - f x) / t < b := by
  have hpath : Tendsto (fun t : ℝ ↦ (x, t)) (𝓝[>] (0 : ℝ)) (clarkeFilter x) :=
    tendsto_const_nhds.prodMk tendsto_id
  exact hpath.eventually (eventually_lt_of_limsup_lt hb
    ⟨_, (eventually_abs_clarkeQuotient_le hU hL d).mono fun _ hp ↦ (abs_le.mp hp).2⟩)

/-- The Clarke directional derivative of a constant function is zero: $f^\circ(x; d) = 0$ for all
$x$ and $d$. -/
theorem clarkeDerivative_const (a : ℝ) (x d : E) :
    clarkeDerivative (fun _ => a) x d = 0 := by
  have hq : clarkeQuotient (fun _ => a) d = fun _ => 0 := by
    funext p
    simp [clarkeQuotient]
  rw [clarkeDerivative, hq]
  exact limsup_const (f := clarkeFilter x) 0

/-- Let $f : E \to \mathbb{R}$ be $L$-Lipschitz on a neighborhood $U$ of $x$. Then
$f^\circ(x; \cdot)$ is subadditive: for all directions $d$ and $e$,
$$f^\circ(x; d + e) \le f^\circ(x; d) + f^\circ(x; e).$$
-/
theorem clarkeDerivative_add_le {f : E → ℝ} {x : E} {U : Set E} {L : ℝ≥0}
    (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith L f U) (d e : E) :
    clarkeDerivative f x (d + e) ≤ clarkeDerivative f x d + clarkeDerivative f x e := by
  let F := clarkeFilter x
  let T (p : E × ℝ) := (p.1 + p.2 • d, p.2)
  let u := clarkeQuotient f d
  let v := clarkeQuotient f e
  have ht : Tendsto T F F := tendsto_clarkeShift x d
  have hu := eventually_abs_clarkeQuotient_le hU hL d
  have hv := eventually_abs_clarkeQuotient_le hU hL e
  have hv' := ht.eventually hv
  have hulo : F.IsBoundedUnder (· ≥ ·) u := ⟨_, hu.mono fun _ h ↦ (abs_le.mp h).1⟩
  have huhi : F.IsBoundedUnder (· ≤ ·) u := ⟨_, hu.mono fun _ h ↦ (abs_le.mp h).2⟩
  have hvhi : F.IsBoundedUnder (· ≤ ·) v := ⟨_, hv.mono fun _ h ↦ (abs_le.mp h).2⟩
  have hv'lo : F.IsBoundedUnder (· ≥ ·) (v ∘ T) := ⟨_, hv'.mono fun _ h ↦ (abs_le.mp h).1⟩
  have hv'hi : F.IsBoundedUnder (· ≤ ·) (v ∘ T) := ⟨_, hv'.mono fun _ h ↦ (abs_le.mp h).2⟩
  have hsplit : clarkeQuotient f (d + e) = u + v ∘ T := by
    funext p
    simp only [u, v, T, clarkeQuotient, Pi.add_apply, Function.comp_apply, smul_add, add_assoc]
    ring
  unfold clarkeDerivative
  rw [hsplit]
  refine (limsup_add_le hulo huhi hv'lo.isCoboundedUnder_le hv'hi).trans (add_le_add_right ?_ _)
  apply ht.limsup_comp_le_limsup _ hvhi
  exact hv'lo.isCoboundedUnder_le

omit [InnerProductSpace ℝ E] in
private theorem tendsto_clarkeScale (x : E) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun p : E × ℝ ↦ (p.1, a * p.2)) (clarkeFilter x) (clarkeFilter x) := by
  have ht : Tendsto Prod.snd (clarkeFilter x) (𝓝[>] (0 : ℝ)) := tendsto_snd
  have hm : Tendsto (fun p : E × ℝ ↦ a * p.2) (clarkeFilter x) (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using (ht.mono_right nhdsWithin_le_nhds).const_mul a
  have hm' : Tendsto (fun p : E × ℝ ↦ a * p.2) (clarkeFilter x) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hm, ?_⟩
    filter_upwards [ht.eventually (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] 0)]
      with p hp
    exact mul_pos ha hp
  exact tendsto_fst.prodMk hm'

/-- Let $f : E \to \mathbb{R}$ be $L$-Lipschitz on a neighborhood $U$ of $x$. Then
$f^\circ(x; \cdot)$ is positively homogeneous: for every $a > 0$ and every direction $d$,
$$f^\circ(x; a d) = a \, f^\circ(x; d).$$
-/
theorem clarkeDerivative_pos_smul {f : E → ℝ} {x : E} {U : Set E} {L : ℝ≥0}
    (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith L f U) {a : ℝ} (ha : 0 < a) (d : E) :
    clarkeDerivative f x (a • d) = a * clarkeDerivative f x d := by
  let F := clarkeFilter x
  let T (p : E × ℝ) := (p.1, a * p.2)
  let S (p : E × ℝ) := (p.1, a⁻¹ * p.2)
  let q := clarkeQuotient f d
  have hm : map T F = F := by
    apply le_antisymm (tendsto_clarkeScale x ha)
    have hTS : T ∘ S = id := by
      funext p
      simp [T, S, ha.ne']
    calc
      F = map T (map S F) := by rw [map_map, hTS, map_id]
      _ ≤ map T F := map_mono (tendsto_clarkeScale x (inv_pos.mpr ha))
  have heq : clarkeQuotient f (a • d) =ᶠ[F] fun p ↦ a * q (T p) := by
    have ht : Tendsto Prod.snd F (𝓝[>] (0 : ℝ)) := tendsto_snd
    filter_upwards [ht.eventually (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] 0)]
      with p hp
    change 0 < p.2 at hp
    simp only [q, T, clarkeQuotient, smul_smul, mul_comm p.2 a]
    field_simp [ha.ne', hp.ne']
  have habs := eventually_abs_clarkeQuotient_le hU hL d
  have hb : F.IsBoundedUnder (· ≤ ·) q := ⟨_, habs.mono fun _ h ↦ (abs_le.mp h).2⟩
  have hl : F.IsBoundedUnder (· ≥ ·) q := ⟨_, habs.mono fun _ h ↦ (abs_le.mp h).1⟩
  have hba : F.IsBoundedUnder (· ≤ ·) (fun p ↦ a * q p) := ⟨a * _, habs.mono
    fun _ h ↦ mul_le_mul_of_nonneg_left (abs_le.mp h).2 ha.le⟩
  have hla : F.IsBoundedUnder (· ≥ ·) (fun p ↦ a * q p) := ⟨a * _, habs.mono
    fun _ h ↦ mul_le_mul_of_nonneg_left (abs_le.mp h).1 ha.le⟩
  unfold clarkeDerivative
  rw [limsup_congr heq, show (fun p ↦ a * q (T p)) = (fun p ↦ a * q p) ∘ T by rfl,
    limsup_comp, hm]
  exact ((OrderIso.mulLeft₀ a ha).limsup_apply hb hl.isCoboundedUnder_le
    hba hla.isCoboundedUnder_le).symm

/-- Let $f : E \to \mathbb{R}$ be $L$-Lipschitz on a neighborhood $U$ of $x$. Then the function
$d \mapsto f^\circ(x; d)$ is $L$-Lipschitz on all of $E$. -/
theorem lipschitzWith_clarkeDerivative {f : E → ℝ} {x : E} {U : Set E} {L : ℝ≥0}
    (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith L f U) : LipschitzWith L (clarkeDerivative f x) := by
  apply LipschitzWith.of_dist_le_mul
  intro d e
  rw [Real.dist_eq, dist_eq_norm, abs_sub_le_iff]
  have h (v w : E) : clarkeDerivative f x v - clarkeDerivative f x w ≤ (L : ℝ) * ‖v - w‖ := by
    have hadd := clarkeDerivative_add_le hU hL (v - w) w
    rw [sub_add_cancel] at hadd
    have hb := (le_abs_self _).trans (abs_clarkeDerivative_le hU hL (v - w))
    linarith
  exact ⟨h d e, by rw [norm_sub_rev d e]; exact h e d⟩

/-- Let $f : E \to \mathbb{R}$ be $L$-Lipschitz on a neighborhood $U$ of $x$, and fix a direction
$d$. If $f^\circ(x; d) < a$, then $f^\circ(y; d) \le a$ for all $y$ in a neighborhood of $x$.
Thus $y \mapsto f^\circ(y; d)$ is upper semicontinuous at $x$. -/
theorem eventually_clarkeDerivative_le_of_lt {f : E → ℝ} {x d : E} {U : Set E}
    {L : ℝ≥0} (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith L f U) {a : ℝ}
    (ha : clarkeDerivative f x d < a) : ∀ᶠ y in 𝓝 x, clarkeDerivative f y d ≤ a := by
  have hb : (clarkeFilter x).IsBoundedUnder (· ≤ ·) (clarkeQuotient f d) :=
    ⟨_, (eventually_abs_clarkeQuotient_le hU hL d).mono fun _ h ↦ (abs_le.mp h).2⟩
  obtain ⟨pa, hp, pb, hpb, hq⟩ := eventually_prod_iff.mp (eventually_lt_of_limsup_lt ha hb)
  obtain ⟨V, hVU, hV, hxV⟩ := _root_.mem_nhds_iff.mp (hp.and hU)
  filter_upwards [hV.mem_nhds hxV] with y hy
  have hVy : ∀ᶠ z in 𝓝 y, z ∈ V := hV.mem_nhds hy
  have hp' : ∀ᶠ z in 𝓝 y, pa z := hVy.mono fun z hz ↦ (hVU hz).1
  have hUy : U ∈ 𝓝 y := hVy.mono fun z hz ↦ (hVU hz).2
  have hl : (clarkeFilter y).IsBoundedUnder (· ≥ ·) (clarkeQuotient f d) :=
    ⟨_, (eventually_abs_clarkeQuotient_le hUy hL d).mono fun _ h ↦ (abs_le.mp h).1⟩
  apply limsup_le_of_le hl.isCoboundedUnder_le
  apply eventually_prod_iff.mpr
  refine ⟨pa, hp', pb, hpb, ?_⟩
  intro z hz t ht
  exact (hq hz ht).le

/-- Let $f : E \to \mathbb{R}$ have the strict Fréchet derivative $A$ at $x$. Then for every
direction $d$,
$$f^\circ(x; d) = A d.$$
This is stated in Section 3.1.4 of [conn2000trust].

No Lipschitz hypothesis is needed: strict differentiability makes the quotients converge. -/
theorem clarkeDerivative_eq_of_hasStrictFDerivAt {f : E → ℝ} {x : E} {A : E →L[ℝ] ℝ}
    (h : HasStrictFDerivAt f A x) (d : E) : clarkeDerivative f x d = A d := by
  apply Filter.Tendsto.limsup_eq
  rw [Metric.tendsto_nhds]
  intro ε hε
  let η := ε / (‖d‖ + 1)
  have hη : 0 < η := div_pos hε (by positivity)
  have hη' : η * ‖d‖ < ε := by
    have hprod : η * (‖d‖ + 1) = ε := div_mul_cancel₀ _ (by positivity)
    linarith
  have hy : Tendsto Prod.fst (clarkeFilter x) (𝓝 x) := tendsto_fst
  have ht : Tendsto Prod.snd (clarkeFilter x) (𝓝[>] (0 : ℝ)) := tendsto_snd
  have hy' : Tendsto (fun p : E × ℝ ↦ p.1 + p.2 • d) (clarkeFilter x) (𝓝 x) :=
    tendsto_fst.comp (tendsto_clarkeShift x d)
  have hprod : Tendsto (fun p : E × ℝ ↦ (p.1 + p.2 • d, p.1)) (clarkeFilter x)
      (𝓝 (x, x)) := hy'.prodMk_nhds hy
  filter_upwards [hprod.eventually (h.isLittleO.def hη),
    ht.eventually (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] 0)] with p hp htp
  change 0 < p.2 at htp
  change ‖f (p.1 + p.2 • d) - f p.1 - A (p.1 + p.2 • d - p.1)‖ ≤
    η * ‖p.1 + p.2 • d - p.1‖ at hp
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos htp] at hp
  rw [Real.dist_eq, clarkeQuotient, show
    (f (p.1 + p.2 • d) - f p.1) / p.2 - A d =
      (f (p.1 + p.2 • d) - f p.1 - A (p.2 • d)) / p.2 by
        rw [map_smul, smul_eq_mul]
        field_simp]
  rw [abs_div, abs_of_pos htp]
  refine ((div_le_iff₀ htp).2 ?_).trans_lt hη'
  convert hp using 1
  ring

/-- The **Clarke subdifferential** of $f : E \to \mathbb{R}$ at $x$ is the set of vectors dominated
by the Clarke directional derivative in every direction:
$$\partial f(x) = \{g \in E \mid \langle g, d \rangle \le f^\circ(x; d) \text{ for all } d \in
  E\}.$$
This is the generalized gradient of Section 3.1.4 of [conn2000trust]. -/
def clarkeSubgradient (f : E → ℝ) (x : E) : Set E :=
  {g | ∀ d : E, ⟪g, d⟫ ≤ clarkeDerivative f x d}

/-- Let $f : E \to \mathbb{R}$ be convex and continuous, and $L$-Lipschitz on a neighborhood $U$ of
$x$. Then every Clarke subgradient of $f$ at $x$ is a subgradient in the sense of convex
analysis: if $g \in \partial f(x)$, then
$$f(x) + \langle z - x, g \rangle \le f(z) \quad \text{for all } z \in E.$$
This step is used in the proof of Theorem 3.2.15 of [conn2000trust].

The Lipschitz hypothesis makes $f^\circ(x; d)$ finite, so that the bound
$\langle g, d \rangle \le f^\circ(x; d)$ has content. The convex subdifferential is
`ConvexAnalysis.subdifferential` for the pairing `innerₗ E` and the function $f$ with values in
`EReal`. -/
theorem clarkeSubgradient_subset_subdifferential {f : E → ℝ} {x : E}
    (hconv : ConvexOn ℝ Set.univ f) (hf : Continuous f)
    {U : Set E} {L : ℝ≥0} (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith L f U) :
    clarkeSubgradient f x ⊆ subdifferential (innerₗ E) (fun z ↦ (f z : EReal)) x := by
  intro g hg z
  let d := z - x
  let F := clarkeFilter x
  have hsec (p : E × ℝ) (hp : 0 < p.2) (ht : p.2 ≤ 1) :
      clarkeQuotient f d p ≤ f (p.1 + d) - f p.1 := by
    have heq : (1 - p.2) • p.1 + p.2 • (p.1 + d) = p.1 + p.2 • d := by
      rw [smul_add, ← add_assoc, ← add_smul, sub_add_cancel, one_smul]
    have h := hconv.2 (Set.mem_univ p.1) (Set.mem_univ (p.1 + d))
      (sub_nonneg.mpr ht) hp.le (sub_add_cancel 1 p.2)
    rw [heq, smul_eq_mul, smul_eq_mul] at h
    change (f (p.1 + p.2 • d) - f p.1) / p.2 ≤ _
    apply (div_le_iff₀ hp).mpr
    linarith
  have hsecF : ∀ᶠ p in F, clarkeQuotient f d p ≤ f (p.1 + d) - f p.1 := by
    have hs : Tendsto Prod.snd F (𝓝[>] (0 : ℝ)) := tendsto_snd
    filter_upwards [hs.eventually (Ioo_mem_nhdsGT (zero_lt_one' ℝ))] with p hp
    exact hsec p hp.1 hp.2.le
  have hyl : Tendsto Prod.fst F (𝓝 x) := tendsto_fst
  have hl : Tendsto (fun p : E × ℝ ↦ f (p.1 + d) - f p.1) F (𝓝 (f (x + d) - f x)) :=
    ((hf.tendsto (x + d)).comp (hyl.add_const d)).sub ((hf.tendsto x).comp hyl)
  have hlow : F.IsBoundedUnder (· ≥ ·) (clarkeQuotient f d) :=
    ⟨_, (eventually_abs_clarkeQuotient_le hU hL d).mono fun _ hp ↦ (abs_le.mp hp).1⟩
  have hlim := limsup_le_limsup hsecF hlow.isCoboundedUnder_le hl.isBoundedUnder_le
  rw [hl.limsup_eq] at hlim
  have hreal : ⟪z - x, g⟫ ≤ f z - f x := by
    have h := (hg d).trans hlim
    simpa [d, real_inner_comm g] using h
  change (f x : EReal) + (⟪z - x, g⟫ : EReal) ≤ f z
  exact_mod_cast (by linarith : f x + ⟪z - x, g⟫ ≤ f z)

/-- The Clarke subdifferential is the intersection, over all directions $d$, of the half-spaces $\{g
\mid \langle g, d \rangle \le f^\circ(x; d)\}$. -/
theorem clarkeSubgradient_eq_iInter (f : E → ℝ) (x : E) :
    clarkeSubgradient f x = ⋂ d : E, {g | ⟪g, d⟫ ≤ clarkeDerivative f x d} := by
  ext g
  simp [clarkeSubgradient]

/-- The Clarke subdifferential $\partial f(x)$ is closed. -/
theorem isClosed_clarkeSubgradient (f : E → ℝ) (x : E) : IsClosed (clarkeSubgradient f x) := by
  rw [clarkeSubgradient_eq_iInter]
  exact isClosed_iInter fun _ ↦ isClosed_le (continuous_id.inner continuous_const) continuous_const

/-- The Clarke subdifferential $\partial f(x)$ is convex. -/
theorem convex_clarkeSubgradient (f : E → ℝ) (x : E) : Convex ℝ (clarkeSubgradient f x) := by
  rw [clarkeSubgradient_eq_iInter]
  refine convex_iInter fun d ↦ ?_
  exact (convex_Iic (clarkeDerivative f x d)).linear_preimage ((innerₗ E).flip d)

/-- Let $E$ be finite-dimensional, and let $f : E \to \mathbb{R}$ be $L$-Lipschitz on a neighborhood
$U$ of $x$. Then the Clarke subdifferential $\partial f(x)$ is compact. This is stated in
Section 3.1.4 of [conn2000trust].

The proof shows that every $g \in \partial f(x)$ has $\|g\| \le L$, and uses that
$\partial f(x)$ is closed. -/
theorem isCompact_clarkeSubgradient [FiniteDimensional ℝ E]
    {f : E → ℝ} {x : E} {U : Set E} {L : ℝ≥0} (hU : U ∈ 𝓝 x)
    (hL : LipschitzOnWith L f U) : IsCompact (clarkeSubgradient f x) := by
  have := FiniteDimensional.proper_real E
  refine (isCompact_closedBall (0 : E) (L : ℝ)).of_isClosed_subset
    (isClosed_clarkeSubgradient f x) fun g hg ↦ ?_
  apply mem_closedBall_zero_iff.mpr
  by_cases hzero : g = 0
  · simp [hzero]
  have h : ⟪g, g⟫ ≤ clarkeDerivative f x g := hg g
  rw [real_inner_self_eq_norm_sq, pow_two] at h
  exact le_of_mul_le_mul_right (h.trans ((le_abs_self _).trans
    (abs_clarkeDerivative_le hU hL g))) (norm_pos_iff.mpr hzero)

/-- The **Clarke support representation** at $x$, equation (3.1.4) of [conn2000trust]: the support
function of the Clarke subdifferential is the Clarke directional derivative,
$$\sup_{g \in \partial f(x)} \langle g, d \rangle = f^\circ(x; d) \quad \text{for all } d \in
  E.$$

The supremum is `ConvexAnalysis.supportFn` for the pairing `innerₗ E`, with values in `EReal`.
The supremum over the empty set is $-\infty$, so the identity implies that $\partial f(x)$ is
nonempty (see `Optimization.HasClarkeSupport.nonempty`). -/
def HasClarkeSupport (f : E → ℝ) (x : E) : Prop :=
  ∀ d, supportFn (innerₗ E) (clarkeSubgradient f x) d = (clarkeDerivative f x d : EReal)

/-- Let $E$ be a real Hilbert space, and let $f : E \to \mathbb{R}$ be $L$-Lipschitz on a
neighborhood $U$ of $x$. Then the support representation (3.1.4) of [conn2000trust] holds at
$x$:
$$\sup_{g \in \partial f(x)} \langle g, d \rangle = f^\circ(x; d) \quad \text{for all } d \in
  E.$$

The function $f^\circ(x; \cdot)$ is positively homogeneous, convex and continuous. A closed
positively homogeneous convex function is the support function of the set of linear functionals
that it dominates, by a separation argument; the proof specializes
`ConvexAnalysis.supportFn_supportSet` with the inner product as the pairing, which uses the
completeness of $E$. -/
theorem hasClarkeSupport_of_lipschitzOnWith [CompleteSpace E]
    {f : E → ℝ} {x : E} {U : Set E} {L : ℝ≥0} (hU : U ∈ 𝓝 x)
    (hL : LipschitzOnWith L f U) : HasClarkeSupport f x := by
  let g (d : E) : EReal := clarkeDerivative f x d
  have hph : PosHomogeneous g := by
    intro a ha d
    simp only [g, clarkeDerivative_pos_smul hU hL ha, EReal.coe_mul]
  have hconv : ConvexFn g := (convexFn_iff_le fun _ ↦ EReal.coe_ne_bot _).2 <| by
    intro d e a b ha hb _
    simp only [← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
    simpa only [clarkeDerivative_pos_smul hU hL ha, clarkeDerivative_pos_smul hU hL hb] using
      clarkeDerivative_add_le hU hL (a • d) (b • e)
  have hcont : Continuous g :=
    continuous_coe_real_ereal.comp (lipschitzWith_clarkeDerivative hU hL).continuous
  have hc : ClosedConvex g :=
    (closedConvex_iff_lowerSemicontinuous fun _ ↦ EReal.coe_ne_bot _).2
      hcont.lowerSemicontinuous
  have hset : supportSet (innerₗ E).flip g = clarkeSubgradient f x := by
    ext z
    simp only [clarkeSubgradient, Set.mem_ofPred_eq, mem_supportSet, g,
      LinearMap.flip_apply, innerₗ_apply_apply, EReal.coe_le_coe_iff]
  have hs := supportFn_supportSet (B := innerₗ E) hph hconv hc ⟨0, EReal.coe_ne_top _⟩
  rw [hset] at hs
  exact congrFun hs

/-- If the support representation (3.1.4) holds at $x$, then the Clarke subdifferential
$\partial f(x)$ is nonempty. -/
theorem HasClarkeSupport.nonempty {f : E → ℝ} {x : E} (h : HasClarkeSupport f x) :
    (clarkeSubgradient f x).Nonempty := by
  by_contra hn
  have h₀ := h 0
  rw [Set.not_nonempty_iff_eq_empty.mp hn, supportFn_empty] at h₀
  exact EReal.bot_ne_coe _ h₀

end Optimization
