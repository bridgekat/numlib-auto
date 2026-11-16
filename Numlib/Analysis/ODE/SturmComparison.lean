/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.ODE.SturmComparison`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The Sturm comparison theorem

Consider two second-order equations $u'' + qu = 0$ and $v'' + Qv = 0$ on an interval, with
$q \le Q$. **Sturm's comparison theorem** says that the zeros of $v$ are at least as dense as those
of $u$: between two consecutive zeros of $u$ there is a zero of $v$. The proof uses the Wronskian
identity
$$(u v' - u' v)' = (q - Q) u v.$$
Suppose $u, v > 0$ on $(a, b)$ and $u(a) = u(b) = 0$. Then the Wronskian $W = u v' - u' v$ is
nonincreasing on $[a, b]$, while $W(a) = -u'(a) v(a) \le 0 \le -u'(b) v(b) = W(b)$, because
$u'(a) \ge 0 \ge u'(b)$ at the zeros of a positive function. When $q < Q$ on $(a, b)$, the Wronskian
is strictly decreasing, and this is a contradiction with no further hypothesis; the zero of $v$ lies
in the open interval. When only $q \le Q$, the hypothesis $u'(a) \neq 0$ gives $W(a) < 0$, and the
zero of $v$ lies in the closed interval. No uniqueness theorem for the equation is used.

Comparison with $\sin(m(x - a))$, which solves $u'' + m^2 u = 0$ and has the consecutive zeros $a$
and $a + \pi/m$, gives two classical corollaries. If $q \ge m^2 > 0$, every solution of
$u'' + qu = 0$ has a zero in every closed interval of length $\pi/m$, and in the open interval when
$q > m^2$. If $q \le M^2$, consecutive zeros are at least $\pi/M$ apart. The presentation follows
Hartman, *Ordinary Differential Equations*, Chapter XI, Theorem 3.1, and Szegő, *Orthogonal
Polynomials*, §1.82.

## Main definitions

* `IsSturmSolutionOn`: $u$ solves $u'' + qu = 0$ on a set $s$, in first-order form $u' = du$,
  $du' = -qu$.

## Main results

* `IsSturmSolutionOn.hasDerivAt_wronskian`: the Wronskian identity $(u v' - u' v)' = (q - Q) u v$.
* `IsSturmSolutionOn.exists_zero_Ioo_of_lt`: Sturm's comparison theorem, strict form, with a zero of
  $v$ in $(a, b)$.
* `IsSturmSolutionOn.exists_zero_Icc_of_le`: Sturm's comparison theorem for $q \le Q$ and
  $u'(a) \neq 0$, with a zero of $v$ in $[a, b]$.
* `IsSturmSolutionOn.exists_zero_Icc_of_sq_le`: if $q \ge m^2 > 0$, every closed interval of length
  $\pi/m$ contains a zero.
* `IsSturmSolutionOn.exists_zero_Ioo_of_sq_lt`: if $q > m^2 > 0$, every open interval of length at
  least $\pi/m$ contains a zero.
* `IsSturmSolutionOn.div_le_sub_of_le_sq`: if $q \le M^2$, consecutive zeros are at least $\pi/M$
  apart.

## Implementation notes

* The statements are about any two functions with the stated second derivatives, given as
  `HasDerivAt` hypotheses in first-order form. The derivative $u'$ is a separate function `du`.
* The bound $\pi/M$ on the distance of zeros comes from the strict comparison theorem applied to a
  slightly faster sine, so that again no uniqueness theorem is needed.
-/

open Set Filter Topology

/-- A function $u$ **solves $u'' + qu = 0$ on $s$**, in first-order form with a function $du$, if at
every point $x \in s$ the function $u$ has the derivative $du(x)$ and the function $du$ has the
derivative $-q(x) u(x)$. -/
structure IsSturmSolutionOn (q u du : ℝ → ℝ) (s : Set ℝ) : Prop where
  /-- The function $u$ has the derivative $du(x)$ at every $x \in s$. -/
  hasDerivAt : ∀ x ∈ s, HasDerivAt u (du x) x
  /-- The function $du$ has the derivative $-q(x) u(x)$ at every $x \in s$. -/
  hasDerivAt_deriv : ∀ x ∈ s, HasDerivAt du (-(q x * u x)) x

/-! ### Sign lemmas at the endpoints -/

/-- Let $a < b$, and let $u : \mathbb{R} \to \mathbb{R}$ have the derivative $du$ at $a$. If
$u(a) = 0$ and $u > 0$ on $(a, b)$, then $du \ge 0$. -/
theorem HasDerivAt.nonneg_of_pos_Ioo {u : ℝ → ℝ} {du a b : ℝ} (hab : a < b)
    (hu : HasDerivAt u du a) (ha : u a = 0) (hpos : ∀ x ∈ Ioo a b, 0 < u x) : 0 ≤ du := by
  refine ge_of_tendsto (hasDerivAt_iff_tendsto_slope_left_right.1 hu).2 ?_
  filter_upwards [Ioo_mem_nhdsGT hab] with x hx
  rw [slope_def_field, ha, sub_zero]
  exact div_nonneg (hpos x hx).le (by linarith [hx.1])

/-- Let $a < b$, and let $u : \mathbb{R} \to \mathbb{R}$ have the derivative $du$ at $b$. If
$u(b) = 0$ and $u > 0$ on $(a, b)$, then $du \le 0$. -/
theorem HasDerivAt.nonpos_of_pos_Ioo {u : ℝ → ℝ} {du a b : ℝ} (hab : a < b)
    (hu : HasDerivAt u du b) (hb : u b = 0) (hpos : ∀ x ∈ Ioo a b, 0 < u x) : du ≤ 0 := by
  refine le_of_tendsto (hasDerivAt_iff_tendsto_slope_left_right.1 hu).1 ?_
  filter_upwards [Ioo_mem_nhdsLT hab] with x hx
  rw [slope_def_field, hb, sub_zero]
  exact div_nonpos_of_nonneg_of_nonpos (hpos x hx).le (by linarith [hx.2])

/-- Let $a < b$, and let $v : \mathbb{R} \to \mathbb{R}$ be continuous at $a$. If $v > 0$ on
$(a, b)$, then $v(a) \ge 0$. -/
theorem ContinuousAt.nonneg_of_pos_Ioo_left {v : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hv : ContinuousAt v a) (hpos : ∀ x ∈ Ioo a b, 0 < v x) : 0 ≤ v a := by
  have := left_nhdsWithin_Ioo_neBot hab
  exact ge_of_tendsto (hv.tendsto.mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall fun x hx => (hpos x hx).le)

/-- Let $a < b$, and let $v : \mathbb{R} \to \mathbb{R}$ be continuous at $b$. If $v > 0$ on
$(a, b)$, then $v(b) \ge 0$. -/
theorem ContinuousAt.nonneg_of_pos_Ioo_right {v : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hv : ContinuousAt v b) (hpos : ∀ x ∈ Ioo a b, 0 < v x) : 0 ≤ v b := by
  have := right_nhdsWithin_Ioo_neBot hab
  exact ge_of_tendsto (hv.tendsto.mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall fun x hx => (hpos x hx).le)

/-- Let $s \subseteq \mathbb{R}$ be preconnected, and let $v$ be continuous on $s$ with
$v(x) \neq 0$ for all $x \in s$. Then either $v > 0$ on $s$ or $v < 0$ on $s$. -/
theorem IsPreconnected.forall_pos_or_forall_neg {v : ℝ → ℝ} {s : Set ℝ} (hs : IsPreconnected s)
    (hv : ContinuousOn v s) (h0 : ∀ x ∈ s, v x ≠ 0) :
    (∀ x ∈ s, 0 < v x) ∨ (∀ x ∈ s, v x < 0) := by
  by_contra h
  push Not at h
  obtain ⟨⟨x, hx, hvx⟩, ⟨y, hy, hvy⟩⟩ := h
  have hvx' : v x < 0 := lt_of_le_of_ne hvx (h0 x hx)
  have hvy' : 0 < v y := lt_of_le_of_ne hvy (h0 y hy).symm
  obtain ⟨z, hz, hvz⟩ := hs.intermediate_value hx hy hv ⟨hvx'.le, hvy'.le⟩
  exact h0 z hz hvz

namespace IsSturmSolutionOn

variable {q u du : ℝ → ℝ} {s : Set ℝ}

/-- If $u$ solves $u'' + qu = 0$ on $s$, it solves the equation on every subset $t \subseteq s$. -/
theorem mono (h : IsSturmSolutionOn q u du s) {t : Set ℝ} (hts : t ⊆ s) :
    IsSturmSolutionOn q u du t :=
  ⟨fun x hx => h.hasDerivAt x (hts hx), fun x hx => h.hasDerivAt_deriv x (hts hx)⟩

/-- If $u$ solves $u'' + qu = 0$ on $s$ with the derivative $du$, then $-u$ solves it on $s$ with
the derivative $-du$. -/
theorem neg (h : IsSturmSolutionOn q u du s) : IsSturmSolutionOn q (-u) (-du) s :=
  ⟨fun x hx => (h.hasDerivAt x hx).neg,
    fun x hx => (h.hasDerivAt_deriv x hx).neg.congr_deriv (by simp only [Pi.neg_apply, mul_neg])⟩

/-- A solution $u$ of $u'' + qu = 0$ on $s$ is continuous on $s$. -/
theorem continuousOn (h : IsSturmSolutionOn q u du s) : ContinuousOn u s :=
  fun x hx => (h.hasDerivAt x hx).continuousAt.continuousWithinAt

/-- The derivative $du$ of a solution of $u'' + qu = 0$ on $s$ is continuous on $s$. -/
theorem continuousOn_deriv (h : IsSturmSolutionOn q u du s) : ContinuousOn du s :=
  fun x hx => (h.hasDerivAt_deriv x hx).continuousAt.continuousWithinAt

/-- **The Wronskian identity.** Let $u$ solve $u'' + qu = 0$ on $s$ with the derivative $du$, and
let $v$ solve $v'' + Qv = 0$ on $s$ with the derivative $dv$. Then at every $x \in s$ the
Wronskian $y \mapsto u(y)\, dv(y) - du(y)\, v(y)$ has the derivative
$$(q(x) - Q(x)) u(x) v(x).$$
-/
theorem hasDerivAt_wronskian {Q v dv : ℝ → ℝ} (hu : IsSturmSolutionOn q u du s)
    (hv : IsSturmSolutionOn Q v dv s) {x : ℝ} (hx : x ∈ s) :
    HasDerivAt (fun y => u y * dv y - du y * v y) ((q x - Q x) * (u x * v x)) x :=
  (((hu.hasDerivAt x hx).mul (hv.hasDerivAt_deriv x hx)).sub
    ((hu.hasDerivAt_deriv x hx).mul (hv.hasDerivAt x hx))).congr_deriv (by ring)

/-- **The Wronskian is nonincreasing.** Let $a \le b$, let $u$ solve $u'' + qu = 0$ and $v$ solve
$v'' + Qv = 0$ on $[a, b]$, and assume $q \le Q$ and $uv \ge 0$ on $(a, b)$. Then
$$u(b) v'(b) - u'(b) v(b) \le u(a) v'(a) - u'(a) v(a).$$
-/
theorem wronskian_apply_le {Q v dv : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hu : IsSturmSolutionOn q u du (Icc a b)) (hv : IsSturmSolutionOn Q v dv (Icc a b))
    (hqQ : ∀ x ∈ Ioo a b, q x ≤ Q x) (huv : ∀ x ∈ Ioo a b, 0 ≤ u x * v x) :
    u b * dv b - du b * v b ≤ u a * dv a - du a * v a := by
  have hW : ∀ x ∈ Icc a b,
      HasDerivAt (fun y => u y * dv y - du y * v y) ((q x - Q x) * (u x * v x)) x :=
    fun x hx => hu.hasDerivAt_wronskian hv hx
  refine antitoneOn_of_deriv_nonpos (convex_Icc a b)
    (fun x hx => (hW x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hW x (interior_subset hx)).differentiableAt.differentiableWithinAt)
    (fun x hx => ?_) (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hab
  rw [interior_Icc] at hx
  rw [(hW x (Ioo_subset_Icc_self hx)).deriv]
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hqQ x hx]) (huv x hx)

/-- **The Wronskian is strictly decreasing.** Let $a < b$, let $u$ solve $u'' + qu = 0$ and $v$
solve $v'' + Qv = 0$ on $[a, b]$, and assume $q < Q$ and $uv > 0$ on $(a, b)$. Then
$$u(b) v'(b) - u'(b) v(b) < u(a) v'(a) - u'(a) v(a).$$
-/
theorem wronskian_apply_lt {Q v dv : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hu : IsSturmSolutionOn q u du (Icc a b)) (hv : IsSturmSolutionOn Q v dv (Icc a b))
    (hqQ : ∀ x ∈ Ioo a b, q x < Q x) (huv : ∀ x ∈ Ioo a b, 0 < u x * v x) :
    u b * dv b - du b * v b < u a * dv a - du a * v a := by
  have hW : ∀ x ∈ Icc a b,
      HasDerivAt (fun y => u y * dv y - du y * v y) ((q x - Q x) * (u x * v x)) x :=
    fun x hx => hu.hasDerivAt_wronskian hv hx
  refine strictAntiOn_of_deriv_neg (convex_Icc a b)
    (fun x hx => (hW x hx).continuousAt.continuousWithinAt)
    (fun x hx => ?_) (left_mem_Icc.2 hab.le) (right_mem_Icc.2 hab.le) hab
  rw [interior_Icc] at hx
  rw [(hW x (Ioo_subset_Icc_self hx)).deriv]
  exact mul_neg_of_neg_of_pos (by linarith [hqQ x hx]) (huv x hx)

/-- The strict comparison in the positive case: the conditions $u, v > 0$ on $(a, b)$,
$u(a) = u(b) = 0$ and $q < Q$ on $(a, b)$ cannot all hold. -/
private theorem not_pos_of_lt {Q v dv : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hu : IsSturmSolutionOn q u du (Icc a b)) (hv : IsSturmSolutionOn Q v dv (Icc a b))
    (hqQ : ∀ x ∈ Ioo a b, q x < Q x) (hua : u a = 0) (hub : u b = 0)
    (hupos : ∀ x ∈ Ioo a b, 0 < u x) (hvpos : ∀ x ∈ Ioo a b, 0 < v x) : False := by
  have hW := hu.wronskian_apply_lt hab hv hqQ fun x hx => mul_pos (hupos x hx) (hvpos x hx)
  have hdua : 0 ≤ du a :=
    (hu.hasDerivAt a (left_mem_Icc.2 hab.le)).nonneg_of_pos_Ioo hab hua hupos
  have hdub : du b ≤ 0 :=
    (hu.hasDerivAt b (right_mem_Icc.2 hab.le)).nonpos_of_pos_Ioo hab hub hupos
  have hva : 0 ≤ v a :=
    (hv.hasDerivAt a (left_mem_Icc.2 hab.le)).continuousAt.nonneg_of_pos_Ioo_left hab hvpos
  have hvb : 0 ≤ v b :=
    (hv.hasDerivAt b (right_mem_Icc.2 hab.le)).continuousAt.nonneg_of_pos_Ioo_right hab hvpos
  rw [hua, hub, zero_mul, zero_mul, zero_sub, zero_sub, neg_lt_neg_iff] at hW
  nlinarith [mul_nonneg hdua hva, mul_nonpos_of_nonpos_of_nonneg hdub hvb]

/-- **Sturm's comparison theorem, strict form.** Let $a < b$, let $u$ solve $u'' + qu = 0$ and $v$
solve $v'' + Qv = 0$ on $[a, b]$, and assume $q < Q$ on $(a, b)$. If $a$ and $b$ are consecutive
zeros of $u$, that is, $u(a) = u(b) = 0$ and $u \neq 0$ on $(a, b)$, then $v$ has a zero in the
open interval $(a, b)$. -/
theorem exists_zero_Ioo_of_lt {Q v dv : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hu : IsSturmSolutionOn q u du (Icc a b)) (hv : IsSturmSolutionOn Q v dv (Icc a b))
    (hqQ : ∀ x ∈ Ioo a b, q x < Q x) (hua : u a = 0) (hub : u b = 0)
    (hu0 : ∀ x ∈ Ioo a b, u x ≠ 0) : ∃ x ∈ Ioo a b, v x = 0 := by
  by_contra hne
  push Not at hne
  have hus := isPreconnected_Ioo.forall_pos_or_forall_neg
    (hu.continuousOn.mono Ioo_subset_Icc_self) hu0
  have hvs := isPreconnected_Ioo.forall_pos_or_forall_neg
    (hv.continuousOn.mono Ioo_subset_Icc_self) hne
  have hua' : (-u) a = 0 := by simp [hua]
  have hub' : (-u) b = 0 := by simp [hub]
  rcases hus with hupos | huneg <;> rcases hvs with hvpos | hvneg
  · exact not_pos_of_lt hab hu hv hqQ hua hub hupos hvpos
  · exact not_pos_of_lt hab hu hv.neg hqQ hua hub hupos
      fun x hx => by simpa using hvneg x hx
  · exact not_pos_of_lt hab hu.neg hv hqQ hua' hub' (fun x hx => by simpa using huneg x hx) hvpos
  · exact not_pos_of_lt hab hu.neg hv.neg hqQ hua' hub' (fun x hx => by simpa using huneg x hx)
      fun x hx => by simpa using hvneg x hx

/-- The non-strict comparison in the positive case: the conditions $u > 0$ on $(a, b)$, $v > 0$ on
$[a, b]$, $u(a) = u(b) = 0$, $u'(a) \neq 0$ and $q \le Q$ on $(a, b)$ cannot all hold. -/
private theorem not_pos_of_le {Q v dv : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hu : IsSturmSolutionOn q u du (Icc a b)) (hv : IsSturmSolutionOn Q v dv (Icc a b))
    (hqQ : ∀ x ∈ Ioo a b, q x ≤ Q x) (hua : u a = 0) (hub : u b = 0) (hdua : du a ≠ 0)
    (hupos : ∀ x ∈ Ioo a b, 0 < u x) (hvpos : ∀ x ∈ Icc a b, 0 < v x) : False := by
  have hW := hu.wronskian_apply_le hab.le hv hqQ fun x hx =>
    (mul_pos (hupos x hx) (hvpos x (Ioo_subset_Icc_self hx))).le
  have hdua' : 0 ≤ du a :=
    (hu.hasDerivAt a (left_mem_Icc.2 hab.le)).nonneg_of_pos_Ioo hab hua hupos
  have hdub : du b ≤ 0 :=
    (hu.hasDerivAt b (right_mem_Icc.2 hab.le)).nonpos_of_pos_Ioo hab hub hupos
  have hva : 0 < v a := hvpos a (left_mem_Icc.2 hab.le)
  have hvb : 0 < v b := hvpos b (right_mem_Icc.2 hab.le)
  have hdua'' : 0 < du a := lt_of_le_of_ne hdua' (Ne.symm hdua)
  rw [hua, hub, zero_mul, zero_mul, zero_sub, zero_sub, neg_le_neg_iff] at hW
  nlinarith [mul_pos hdua'' hva, mul_nonpos_of_nonpos_of_nonneg hdub hvb.le]

/-- **Sturm's comparison theorem.** Let $a < b$, let $u$ solve $u'' + qu = 0$ and $v$ solve
$v'' + Qv = 0$ on $[a, b]$, and assume $q \le Q$ on $(a, b)$. If $a$ and $b$ are consecutive
zeros of $u$, that is, $u(a) = u(b) = 0$ and $u \neq 0$ on $(a, b)$, and if $u'(a) \neq 0$, then
$v$ has a zero in the closed interval $[a, b]$.

The hypothesis $u'(a) \neq 0$ replaces the uniqueness theorem for the equation, by which a
solution with $u(a) = u'(a) = 0$ vanishes identically. It holds for every explicit comparison
function such as $\sin(m(x - a))$. -/
theorem exists_zero_Icc_of_le {Q v dv : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hu : IsSturmSolutionOn q u du (Icc a b)) (hv : IsSturmSolutionOn Q v dv (Icc a b))
    (hqQ : ∀ x ∈ Ioo a b, q x ≤ Q x) (hua : u a = 0) (hub : u b = 0)
    (hu0 : ∀ x ∈ Ioo a b, u x ≠ 0) (hdua : du a ≠ 0) : ∃ x ∈ Icc a b, v x = 0 := by
  by_contra hne
  push Not at hne
  have hus := isPreconnected_Ioo.forall_pos_or_forall_neg
    (hu.continuousOn.mono Ioo_subset_Icc_self) hu0
  have hvs := isPreconnected_Icc.forall_pos_or_forall_neg hv.continuousOn hne
  have hua' : (-u) a = 0 := by simp [hua]
  have hub' : (-u) b = 0 := by simp [hub]
  have hdua' : (-du) a ≠ 0 := by simpa using hdua
  rcases hus with hupos | huneg <;> rcases hvs with hvpos | hvneg
  · exact not_pos_of_le hab hu hv hqQ hua hub hdua hupos hvpos
  · exact not_pos_of_le hab hu hv.neg hqQ hua hub hdua hupos
      fun x hx => by simpa using hvneg x hx
  · exact not_pos_of_le hab hu.neg hv hqQ hua' hub' hdua'
      (fun x hx => by simpa using huneg x hx) hvpos
  · exact not_pos_of_le hab hu.neg hv.neg hqQ hua' hub' hdua'
      (fun x hx => by simpa using huneg x hx) fun x hx => by simpa using hvneg x hx

end IsSturmSolutionOn

/-! ### Comparison with the sine -/

open Real in
/-- For $m, c \in \mathbb{R}$, the function $x \mapsto \sin(mx + c)$ solves $u'' + m^2 u = 0$ on
$\mathbb{R}$, with the derivative $x \mapsto m \cos(mx + c)$. -/
theorem isSturmSolutionOn_sin (m c : ℝ) :
    IsSturmSolutionOn (fun _ => m ^ 2) (fun x => sin (m * x + c))
      (fun x => m * cos (m * x + c)) univ := by
  have hl : ∀ x : ℝ, HasDerivAt (fun x => m * x + c) m x := fun x => by
    simpa using ((hasDerivAt_id x).const_mul m).add_const c
  refine ⟨fun x _ => ?_, fun x _ => ?_⟩
  · exact ((Real.hasDerivAt_sin _).comp x (hl x)).congr_deriv (by ring)
  · exact (((Real.hasDerivAt_cos _).comp x (hl x)).const_mul m).congr_deriv (by ring)

namespace IsSturmSolutionOn

open Real

variable {q u du : ℝ → ℝ}

/-- **Zeros of a solution with $q \ge m^2 > 0$.** Let $m > 0$ and $b - a \ge \pi/m$. If $u$ solves
$u'' + qu = 0$ on $[a, b]$ and $q \ge m^2$ on $[a, b]$, then $u$ has a zero in $[a, b]$.

The proof compares $u$ with $\sin(m(x - a))$, whose consecutive zeros are $a$ and $a + \pi/m$. -/
theorem exists_zero_Icc_of_sq_le {a b m : ℝ} (hm : 0 < m) (hab : π / m ≤ b - a)
    (hu : IsSturmSolutionOn q u du (Icc a b)) (hq : ∀ x ∈ Icc a b, m ^ 2 ≤ q x) :
    ∃ x ∈ Icc a b, u x = 0 := by
  have hπ : 0 < π / m := div_pos pi_pos hm
  have hc : a + π / m ≤ b := by linarith
  have hsub : Icc a (a + π / m) ⊆ Icc a b := Icc_subset_Icc le_rfl hc
  have hsin : ∀ x ∈ Ioo a (a + π / m), sin (m * x + -(m * a)) ≠ 0 := by
    intro x hx
    refine (sin_pos_of_pos_of_lt_pi ?_ ?_).ne'
    · nlinarith [hx.1]
    · have : m * x < m * (a + π / m) := mul_lt_mul_of_pos_left hx.2 hm
      rw [mul_add, mul_div_cancel₀ _ hm.ne'] at this
      linarith
  obtain ⟨x, hx, hux⟩ := (isSturmSolutionOn_sin m (-(m * a))).mono (subset_univ _)
    |>.exists_zero_Icc_of_le (Q := q) (v := u) (dv := du) (by linarith) (hu.mono hsub)
      (fun x hx => hq x (hsub (Ioo_subset_Icc_self hx)))
      (by simp) (by rw [show m * (a + π / m) + -(m * a) = π by field_simp; ring]; exact sin_pi)
      hsin (by simp [hm.ne'])
  exact ⟨x, hsub hx, hux⟩

/-- **Zeros of a solution with $q > m^2 > 0$.** Let $m > 0$ and $b - a \ge \pi/m$. If $u$ solves
$u'' + qu = 0$ on $[a, b]$ and $q > m^2$ on $(a, b)$, then $u$ has a zero in the open interval
$(a, b)$.

The proof is the strict comparison with $\sin(m(x - a))$. -/
theorem exists_zero_Ioo_of_sq_lt {a b m : ℝ} (hm : 0 < m) (hab : π / m ≤ b - a)
    (hu : IsSturmSolutionOn q u du (Icc a b)) (hq : ∀ x ∈ Ioo a b, m ^ 2 < q x) :
    ∃ x ∈ Ioo a b, u x = 0 := by
  have hπ : 0 < π / m := div_pos pi_pos hm
  have hc : a + π / m ≤ b := by linarith
  have hsub : Icc a (a + π / m) ⊆ Icc a b := Icc_subset_Icc le_rfl hc
  have hsub' : Ioo a (a + π / m) ⊆ Ioo a b := Ioo_subset_Ioo le_rfl hc
  have hsin : ∀ x ∈ Ioo a (a + π / m), sin (m * x + -(m * a)) ≠ 0 := by
    intro x hx
    refine (sin_pos_of_pos_of_lt_pi ?_ ?_).ne'
    · nlinarith [hx.1]
    · have : m * x < m * (a + π / m) := mul_lt_mul_of_pos_left hx.2 hm
      rw [mul_add, mul_div_cancel₀ _ hm.ne'] at this
      linarith
  obtain ⟨x, hx, hux⟩ := (isSturmSolutionOn_sin m (-(m * a))).mono (subset_univ _)
    |>.exists_zero_Ioo_of_lt (Q := q) (v := u) (dv := du) (by linarith) (hu.mono hsub)
      (fun x hx => hq x (hsub' hx))
      (by simp) (by rw [show m * (a + π / m) + -(m * a) = π by field_simp; ring]; exact sin_pi)
      hsin
  exact ⟨x, hsub' hx, hux⟩

/-- **Consecutive zeros of a solution with $q \le M^2$ are at least $\pi/M$ apart.** Let $M > 0$ and
$a < b$. Let $u$ solve $u'' + qu = 0$ on $[a, b]$ with $q \le M^2$ on $(a, b)$. If
$u(a) = u(b) = 0$ and $u \neq 0$ on $(a, b)$, then $b - a \ge \pi/M$.

Proof idea: if $b - a < \pi/M$, take a sine $\sin(M'(x - a) + \delta)$ with $M < M'$,
$M'(b - a) < \pi$ and a small phase $\delta > 0$. It is positive on $[a, b]$ and solves
$w'' + M'^2 w = 0$ with $M'^2 > q$, which the strict comparison theorem forbids. -/
theorem div_le_sub_of_le_sq {a b M : ℝ} (hM : 0 < M) (hab : a < b)
    (hu : IsSturmSolutionOn q u du (Icc a b)) (hq : ∀ x ∈ Ioo a b, q x ≤ M ^ 2)
    (hua : u a = 0) (hub : u b = 0) (hu0 : ∀ x ∈ Ioo a b, u x ≠ 0) : π / M ≤ b - a := by
  by_contra hlt
  push Not at hlt
  have hba : 0 < b - a := by linarith
  have hMab : M * (b - a) < π := by
    have := (lt_div_iff₀ hM).1 hlt
    linarith
  set M' : ℝ := (M + π / (b - a)) / 2 with hM'
  have hM'ab : M' * (b - a) = (M * (b - a) + π) / 2 := by
    rw [hM']; field_simp
  have hMM' : M < M' := by
    rw [hM']
    have : M < π / (b - a) := by rwa [lt_div_iff₀ hba]
    linarith
  have hM'π : M' * (b - a) < π := by linarith
  set δ : ℝ := (π - M' * (b - a)) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hM'pos : 0 < M' := hM.trans hMM'
  -- the comparison sine is positive on `[a, b]`
  have hwpos : ∀ x ∈ Icc a b, 0 < sin (M' * x + (δ - M' * a)) := by
    intro x hx
    refine sin_pos_of_pos_of_lt_pi ?_ ?_
    · nlinarith [hx.1]
    · have : M' * x ≤ M' * b := mul_le_mul_of_nonneg_left hx.2 hM'pos.le
      rw [hδ]; nlinarith
  obtain ⟨x, hx, hwx⟩ := hu.exists_zero_Ioo_of_lt hab
    ((isSturmSolutionOn_sin M' (δ - M' * a)).mono (subset_univ _))
    (fun x hx => (hq x hx).trans_lt (by gcongr)) hua hub hu0
  exact (hwpos x (Ioo_subset_Icc_self hx)).ne' hwx

end IsSturmSolutionOn
