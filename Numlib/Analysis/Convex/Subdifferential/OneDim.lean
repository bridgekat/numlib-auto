/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Closure
import Numlib.Analysis.Convex.Operations.Closed
import Numlib.Analysis.Convex.Subdifferential.Monotone

/-!
# One-sided derivatives of a convex function on the line

A convex function $f \colon \mathbb{R} \to [-\infty, +\infty]$ has a right derivative $f'_+(x)$ and
a left derivative $f'_-(x)$ at every point, with values in $[-\infty, +\infty]$, and these carry all
the first-order information:
$$\partial f(x) = \{x^* \in \mathbb{R} \mid f'_-(x) \le x^* \le f'_+(x)\}.$$
Both are nondecreasing, they interlace as $f'_+(z_1) \le f'_-(x) \le f'_+(x) \le f'_-(z_2)$ for
$z_1 < x < z_2$, and both are real exactly on $\operatorname{int}(\operatorname{dom} f)$. When $f$
is closed, each is a one-sided limit of the other: $f'_+(z)$ and $f'_-(z)$ both tend to $f'_+(x)$ as
$z \downarrow x$, and to $f'_-(x)$ as $z \uparrow x$. So $f'_+$ is right-continuous, $f'_-$ is
left-continuous, and each determines the other. Hence any nondecreasing $\varphi$ with
$f'_- \le \varphi \le f'_+$ determines $\partial f$, and so determines $f$ up to an additive
constant. The presentation follows [rockafellar1970convex], §23 and §24.

On the line, the two notions of monotonicity of `Numlib.Analysis.Convex.Subdifferential.Monotone`
agree. A monotone relation on $\mathbb{R}$ is a subset of $\mathbb{R} \times \mathbb{R}$ that is
totally ordered by the coordinatewise order, a **non-decreasing curve**. A cycle through such a set
can be rotated so that it starts at its largest pair. This pair dominates the cycle in both
coordinates, and its deletion does not decrease the telescoping sum. So monotone and cyclically
monotone relations on the line are the same, and the maximal monotone relations, the **complete
non-decreasing curves**, are exactly the graphs of the subdifferentials of the closed proper convex
functions.

## Main definitions

* `ConvexAnalysis.rightDeriv`, `ConvexAnalysis.leftDeriv`: the right and left derivatives $f'_+$ and
  $f'_-$, extended by $+\infty$ to the right of $\operatorname{dom} f$ and by $-\infty$ to its left.
* `ConvexAnalysis.cycleVal`: the telescoping sum around a cycle given as one list of pairs, the form
  in which rotations can be expressed.

## Main results

* `ConvexAnalysis.mem_subdifferential_iff_le_rightDeriv`: $\partial f(x)$ is the set of real numbers
  in $[f'_-(x), f'_+(x)]$.
* `ConvexAnalysis.iInf_rightDeriv_Ioi`, `ConvexAnalysis.iSup_leftDeriv_Iio`,
  `ConvexAnalysis.iInf_leftDeriv_Ioi`, `ConvexAnalysis.iSup_rightDeriv_Iio`: the four one-sided
  limit formulas for a closed proper convex $f$, also in the form of limits as
  `ConvexAnalysis.tendsto_rightDeriv_nhdsWithin_Ioi` and its three companions.
* `ConvexAnalysis.exists_eq_add_coe_of_le_le`: two closed proper convex functions whose one-sided
  derivatives enclose the same $\varphi$ differ by a constant.
* `ConvexAnalysis.IsMonotoneRel.isCyclicallyMonotone`: on the line, every monotone relation is
  cyclically monotone.
* `ConvexAnalysis.isMaximalMonotoneRel_iff_exists_closedProperConvexFn`: the maximal monotone
  relations on the line are exactly the graphs of the subdifferentials of the closed proper convex
  functions ([rockafellar1970convex], Theorem 24.3).

## Implementation notes

* $f'_+(x)$ is $f'(x; 1)$ and $f'_-(x)$ is $-f'(x; -1)$, so the theory of `ConvexAnalysis.dirDeriv`
  applies and nothing is defined again. Both definitions have a guard: $f'_+(x)$ is $f'(x; 1)$ if
  some point of $\operatorname{dom} f$ lies to the right of $x$, and $+\infty$ otherwise. The guard
  is necessary because at a point where $f(x) = +\infty$ every difference quotient is
  $(+\infty) - (+\infty) = -\infty$ in `EReal`. Without the guard, the infimum would be $-\infty$ on
  both sides of $\operatorname{dom} f$, and the two sides must be told apart. Where $f$ is finite
  the guard has no effect.
* The reflection $t \mapsto -t$ exchanges the two sides:
  `ConvexAnalysis.leftDeriv_eq_neg_rightDeriv_comp_neg` states
  $f'_-(x) = -(f \circ \operatorname{neg})'_+(-x)$. The results on $f'_-$ are derived through it
  from the results on $f'_+$. The one-sided limits of a monotone function are Mathlib's
  `Monotone.tendsto_nhdsGT` and `Monotone.tendsto_nhdsLT`.
-/

open Set Filter Topology

namespace ConvexAnalysis

/-! ### The directional derivative outside the effective domain -/

section Outside

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {f : E → EReal} {x : E}

/-- If $f(x) = +\infty$, then every difference quotient at $x$ is $-\infty$, so $f'(x; y) = -\infty$
for every direction $y$. This is the correct value of $f'_+(x)$ to the left of
$\operatorname{dom} f$. To the right of $\operatorname{dom} f$, the definition of
`ConvexAnalysis.rightDeriv` replaces it by $+\infty$. -/
theorem dirDeriv_eq_bot_of_eq_top (hx : f x = ⊤) (y : E) : dirDeriv f x y = ⊥ := by
  refine le_antisymm ?_ bot_le
  refine (dirDeriv_le f x y one_pos).trans ?_
  rw [hx, EReal.sub_top,
    EReal.bot_div_of_pos_ne_top (by exact_mod_cast one_pos) (EReal.coe_ne_top 1)]

end Outside

/-! ### The right and left derivatives -/

section Defs

variable {f : ℝ → EReal} {x : ℝ}

/-- The **right derivative** of a function $f \colon \mathbb{R} \to [-\infty, +\infty]$ at $x$:
$$f'_+(x) = f'(x; 1) = \inf_{a > 0} \frac{f(x + a) - f(x)}{a}$$
if $f(z) < +\infty$ for some $z > x$, and $f'_+(x) = +\infty$ otherwise.

For a convex $f$ that is finite at $x$, the difference quotient is nondecreasing in $a$, so
$f'_+(x)$ is the limit $\lim_{z \downarrow x} (f(z) - f(x))/(z - x)$. Without the second case,
all difference quotients at a point to the right of $\operatorname{dom} f$ would be $-\infty$,
which is the value for the points to the left of $\operatorname{dom} f$. -/
noncomputable def rightDeriv (f : ℝ → EReal) (x : ℝ) : EReal :=
  ⨅ _ : ∃ z, x < z ∧ f z < ⊤, dirDeriv f x 1

/-- The **left derivative** of a function $f \colon \mathbb{R} \to [-\infty, +\infty]$ at $x$:
$$f'_-(x) = -f'(x; -1)$$
if $f(z) < +\infty$ for some $z < x$, and $f'_-(x) = -\infty$ otherwise.

For a convex $f$ that is finite at $x$, this is the limit
$\lim_{z \uparrow x} (f(z) - f(x))/(z - x)$. The sign is $-f'(x; -1)$ because the increment
$z - x$ is negative. -/
noncomputable def leftDeriv (f : ℝ → EReal) (x : ℝ) : EReal :=
  ⨆ _ : ∃ z, z < x ∧ f z < ⊤, -dirDeriv f x (-1)

/-- If some point of $\operatorname{dom} f$ lies to the right of $x$, then $f'_+(x) = f'(x; 1)$. -/
theorem rightDeriv_of_exists (h : ∃ z, x < z ∧ f z < ⊤) :
    rightDeriv f x = dirDeriv f x 1 := iInf_pos h

/-- If no point of $\operatorname{dom} f$ lies to the right of $x$, then $f'_+(x) = +\infty$. -/
theorem rightDeriv_of_not_exists (h : ¬∃ z, x < z ∧ f z < ⊤) : rightDeriv f x = ⊤ := iInf_neg h

/-- If some point of $\operatorname{dom} f$ lies to the left of $x$, then $f'_-(x) = -f'(x; -1)$. -/
theorem leftDeriv_of_exists (h : ∃ z, z < x ∧ f z < ⊤) :
    leftDeriv f x = -dirDeriv f x (-1) := iSup_pos h

/-- If no point of $\operatorname{dom} f$ lies to the left of $x$, then $f'_-(x) = -\infty$. -/
theorem leftDeriv_of_not_exists (h : ¬∃ z, z < x ∧ f z < ⊤) : leftDeriv f x = ⊥ := iSup_neg h

/-- If $f(x) = +\infty$ and some point of $\operatorname{dom} f$ lies to the right of $x$, then
$f'_+(x) = -\infty$. To the right of $\operatorname{dom} f$, the right derivative is $+\infty$
by definition. -/
theorem rightDeriv_eq_bot_of_eq_top (hx : f x = ⊤) (h : ∃ z, x < z ∧ f z < ⊤) :
    rightDeriv f x = ⊥ := by
  rw [rightDeriv_of_exists h, dirDeriv_eq_bot_of_eq_top hx]

/-- If $f(x) = +\infty$ and some point of $\operatorname{dom} f$ lies to the left of $x$, then
$f'_-(x) = +\infty$. To the left of $\operatorname{dom} f$, the left derivative is $-\infty$ by
definition. -/
theorem leftDeriv_eq_top_of_eq_top (hx : f x = ⊤) (h : ∃ z, z < x ∧ f z < ⊤) :
    leftDeriv f x = ⊤ := by
  rw [leftDeriv_of_exists h, dirDeriv_eq_bot_of_eq_top hx, EReal.neg_bot]

end Defs

/-!
### Reflection

The reflection $t \mapsto -t$ exchanges the two sides:
$f'_-(x) = -(f \circ \operatorname{neg})'_+(-x)$. The results on $f'_-$ below are proved in this way
from the results on $f'_+$. The reflected function is again closed, proper and convex.
-/

section Reflection

section General

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {f : E → EReal}

/-- For $f \colon E \to [-\infty, +\infty]$, the reflected function $t \mapsto f(-t)$ has the
directional derivative $f'(x; -v)$ at $-x$ in the direction $v$. -/
theorem dirDeriv_comp_neg (f : E → EReal) (x v : E) :
    dirDeriv (fun t => f (-t)) (-x) v = dirDeriv f x (-v) := by
  simp only [dirDeriv_apply, smul_neg, neg_add_rev, neg_neg, add_comm]

end General

variable {f : ℝ → EReal} {x : ℝ}

/-- The left derivative is the reflected right derivative: for every
$f \colon \mathbb{R} \to [-\infty, +\infty]$ and every $x \in \mathbb{R}$,
$$f'_-(x) = -g'_+(-x), \qquad \text{where } g(t) = f(-t).$$
The identity holds in both cases of the definitions. -/
theorem leftDeriv_eq_neg_rightDeriv_comp_neg (f : ℝ → EReal) (x : ℝ) :
    leftDeriv f x = -rightDeriv (fun t => f (-t)) (-x) := by
  have hex : (∃ z, -x < z ∧ f (-z) < ⊤) ↔ ∃ z, z < x ∧ f z < ⊤ :=
    ⟨fun ⟨z, hz, h⟩ => ⟨-z, by linarith, h⟩,
      fun ⟨z, hz, h⟩ => ⟨-z, by linarith, by simpa using h⟩⟩
  by_cases h : ∃ z, z < x ∧ f z < ⊤
  · rw [leftDeriv_of_exists h, rightDeriv_of_exists (hex.2 h), dirDeriv_comp_neg]
  · rw [leftDeriv_of_not_exists h, rightDeriv_of_not_exists (mt hex.1 h), EReal.neg_top]

/-- The right derivative is the reflected left derivative: $f'_+(x) = -g'_-(-x)$, where
$g(t) = f(-t)$. -/
theorem rightDeriv_eq_neg_leftDeriv_comp_neg (f : ℝ → EReal) (x : ℝ) :
    rightDeriv f x = -leftDeriv (fun t => f (-t)) (-x) := by
  simp [leftDeriv_eq_neg_rightDeriv_comp_neg]

end Reflection

/-! ### Monotonicity -/

section Order

variable {f : ℝ → EReal} {x : ℝ}

/-- On the line, the effective domain of a convex function is an interval: if $z_1 \le x \le z_2$
and $f(z_1), f(z_2) < +\infty$, then $f(x) < +\infty$. -/
theorem ConvexFn.lt_top_of_le_of_le (hf : ConvexFn f) {z₁ z₂ : ℝ} (h₁ : f z₁ < ⊤) (h₂ : f z₂ < ⊤)
    (hz₁ : z₁ ≤ x) (hz₂ : x ≤ z₂) : f x < ⊤ :=
  hf.convex_convexDom.ordConnected.out (mem_convexDom.2 h₁) (mem_convexDom.2 h₂)
      (mem_Icc.2 ⟨hz₁, hz₂⟩)

/-- For every $f \colon \mathbb{R} \to [-\infty, +\infty]$ and $x$, $f'(x; 1) \le f'_+(x)$. -/
theorem dirDeriv_le_rightDeriv (f : ℝ → EReal) (x : ℝ) :
    dirDeriv f x 1 ≤ rightDeriv f x := by
  rcases em (∃ z, x < z ∧ f z < ⊤) with h | h
  · exact le_of_eq (rightDeriv_of_exists h).symm
  · rw [rightDeriv_of_not_exists h]; exact le_top

/-- For every $f \colon \mathbb{R} \to [-\infty, +\infty]$ and $x$, $f'_-(x) \le -f'(x; -1)$. -/
theorem leftDeriv_le_neg_dirDeriv (f : ℝ → EReal) (x : ℝ) :
    leftDeriv f x ≤ -dirDeriv f x (-1) := by
  rw [leftDeriv_eq_neg_rightDeriv_comp_neg, EReal.neg_le_neg_iff, ← dirDeriv_comp_neg]
  exact dirDeriv_le_rightDeriv _ _

/-- If $f \colon \mathbb{R} \to [-\infty, +\infty]$ is proper and convex, then $f'_-(x) \le f'_+(x)$
for every $x \in \mathbb{R}$. -/
theorem leftDeriv_le_rightDeriv (hf : ConvexFn f) (hp : ProperConvex f) (x : ℝ) :
    leftDeriv f x ≤ rightDeriv f x := by
  rcases lt_or_ge (f x) ⊤ with hx | hx
  · exact (leftDeriv_le_neg_dirDeriv f x).trans
      ((neg_dirDeriv_neg_le hf hx.ne (hp.ne_bot x) 1).trans (dirDeriv_le_rightDeriv f x))
  have hxt : f x = ⊤ := top_le_iff.1 hx
  rcases em (∃ z, x < z ∧ f z < ⊤) with h₂ | h₂
  · rcases em (∃ z, z < x ∧ f z < ⊤) with h₁ | h₁
    · obtain ⟨z₁, hz₁, hfz₁⟩ := h₁
      obtain ⟨z₂, hz₂, hfz₂⟩ := h₂
      exact absurd (hf.lt_top_of_le_of_le hfz₁ hfz₂ hz₁.le hz₂.le) (by rw [hxt]; simp)
    · rw [leftDeriv_of_not_exists h₁]; exact bot_le
  · rw [rightDeriv_of_not_exists h₂]; exact le_top

/-- Let $y < z$ with $f(y) = p$ and $f(z) = q$ real. Then $f'(y; 1) \le (q - p)/(z - y)$: the right
derivative at the left end of an interval is at most the slope across it. This is one term of
the defining infimum, with the step $z - y$. -/
theorem dirDeriv_one_le_slope {y z p q : ℝ} (hyz : y < z) (hfy : f y = (p : EReal))
    (hfz : f z = (q : EReal)) : dirDeriv f y 1 ≤ (((q - p) / (z - y) : ℝ) : EReal) := by
  have hle := dirDeriv_le f y 1 (by linarith : (0 : ℝ) < z - y)
  rwa [show y + (z - y) • (1 : ℝ) = z by rw [smul_eq_mul]; ring, hfy, hfz,
    ← EReal.coe_sub, ← EReal.coe_div] at hle

/-- Let $y < z$ with $f(y) = p$ and $f(z) = q$ real. Then $f'(z; -1) \le (p - q)/(z - y)$. This is
the mirror image of `ConvexAnalysis.dirDeriv_one_le_slope`, at the right end of the interval. -/
theorem dirDeriv_neg_one_le_slope {y z p q : ℝ} (hyz : y < z) (hfy : f y = (p : EReal))
    (hfz : f z = (q : EReal)) : dirDeriv f z (-1) ≤ (((p - q) / (z - y) : ℝ) : EReal) := by
  have := dirDeriv_one_le_slope (f := fun t => f (-t)) (neg_lt_neg hyz) (by simpa using hfz)
    (by simpa using hfy)
  rwa [dirDeriv_comp_neg, sub_neg_eq_add, neg_add_eq_sub] at this

/-- If $f \colon \mathbb{R} \to [-\infty, +\infty]$ is proper and $y < z$, then
$f'_+(y) \le f'_-(z)$.

With $f'_- \le f'_+$ this gives the chain $f'_+(z_1) \le f'_-(x) \le f'_+(x) \le f'_-(z_2)$ for
$z_1 < x < z_2$, and it makes both functions nondecreasing. Convexity is not needed:
`ConvexAnalysis.dirDeriv` is an infimum of difference quotients, not a limit, so the two
quotients across $[y, z]$ bound it from above for every $f$. Only the inequality
$f'_-(x) \le f'_+(x)$ at a single point uses convexity. -/
theorem rightDeriv_le_leftDeriv (hp : ProperConvex f) {y z : ℝ} (hyz : y < z) :
    rightDeriv f y ≤ leftDeriv f z := by
  rcases em (∃ w, y < w ∧ f w < ⊤) with h₂ | h₂
  swap
  · -- nothing of `dom f` lies to the right of `y`, so `f'₊(y) = ⊤` and `z` sits beyond `dom f`
    obtain ⟨w₀, hw₀⟩ := hp.convexDom_nonempty
    have hw₀y : w₀ ≤ y := not_lt.1 fun hlt => h₂ ⟨w₀, hlt, mem_convexDom.1 hw₀⟩
    rw [leftDeriv_eq_top_of_eq_top (top_le_iff.1 (not_lt.1 fun hlt => h₂ ⟨z, hyz, hlt⟩))
      ⟨w₀, lt_of_le_of_lt hw₀y hyz, mem_convexDom.1 hw₀⟩]
    exact le_top
  rcases em (∃ w, w < z ∧ f w < ⊤) with h₁ | h₁
  swap
  · -- nothing of `dom f` lies to the left of `z`, so `f'₋(z) = ⊥` and `y` sits before `dom f`
    obtain ⟨w₀, hw₀⟩ := hp.convexDom_nonempty
    have hzw₀ : z ≤ w₀ := not_lt.1 fun hlt => h₁ ⟨w₀, hlt, mem_convexDom.1 hw₀⟩
    rw [rightDeriv_eq_bot_of_eq_top (top_le_iff.1 (not_lt.1 fun hlt => h₁ ⟨y, hyz, hlt⟩))
      ⟨w₀, lt_of_lt_of_le hyz hzw₀, mem_convexDom.1 hw₀⟩]
    exact bot_le
  rw [rightDeriv_of_exists h₂, leftDeriv_of_exists h₁]
  rcases lt_or_ge (f y) ⊤ with hfy | hfy
  swap
  · rw [dirDeriv_eq_bot_of_eq_top (top_le_iff.1 hfy)]; exact bot_le
  rcases lt_or_ge (f z) ⊤ with hfz | hfz
  swap
  · rw [dirDeriv_eq_bot_of_eq_top (top_le_iff.1 hfz), EReal.neg_bot]; exact le_top
  obtain ⟨p, hp'⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot y) hfy
  obtain ⟨q, hq'⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot z) hfz
  calc dirDeriv f y 1 ≤ (((q - p) / (z - y) : ℝ) : EReal) := dirDeriv_one_le_slope hyz hp' hq'
    _ = -(((p - q) / (z - y) : ℝ) : EReal) := by
        rw [← EReal.coe_neg]; congr 1; ring
    _ ≤ -dirDeriv f z (-1) :=
        EReal.neg_le_neg_iff.2 (dirDeriv_neg_one_le_slope hyz hp' hq')

/-- If $f \colon \mathbb{R} \to [-\infty, +\infty]$ is proper and convex, then $f'_+$ is
nondecreasing on $\mathbb{R}$. -/
theorem monotone_rightDeriv (hf : ConvexFn f) (hp : ProperConvex f) : Monotone (rightDeriv f) := by
  intro y z hyz
  rcases eq_or_lt_of_le hyz with rfl | hlt
  · exact le_rfl
  exact (rightDeriv_le_leftDeriv hp hlt).trans (leftDeriv_le_rightDeriv hf hp z)

/-- If $f \colon \mathbb{R} \to [-\infty, +\infty]$ is proper and convex, then $f'_-$ is
nondecreasing on $\mathbb{R}$. -/
theorem monotone_leftDeriv (hf : ConvexFn f) (hp : ProperConvex f) : Monotone (leftDeriv f) := by
  intro y z hyz
  rcases eq_or_lt_of_le hyz with rfl | hlt
  · exact le_rfl
  exact (leftDeriv_le_rightDeriv hf hp y).trans (rightDeriv_le_leftDeriv hp hlt)

end Order

/-! ### Finiteness -/

section Finite

variable {f : ℝ → EReal} {x : ℝ}

/-- If $f \colon \mathbb{R} \to [-\infty, +\infty]$ is proper, then $f'_+(x) < +\infty$ if and only
if some point of $\operatorname{dom} f$ lies strictly to the right of $x$. -/
theorem rightDeriv_lt_top_iff (hp : ProperConvex f) :
    rightDeriv f x < ⊤ ↔ ∃ z, x < z ∧ f z < ⊤ := by
  refine ⟨fun h => by_contra fun hcon => ?_, fun h => ?_⟩
  · rw [rightDeriv_of_not_exists hcon] at h
    exact lt_irrefl _ h
  obtain ⟨z, hz, hfz⟩ := h
  rw [rightDeriv_of_exists ⟨z, hz, hfz⟩]
  rcases lt_or_ge (f x) ⊤ with hx | hx
  · obtain ⟨p, hp'⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot x) hx
    obtain ⟨q, hq'⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot z) hfz
    exact lt_of_le_of_lt (dirDeriv_one_le_slope hz hp' hq') (EReal.coe_lt_top _)
  · rw [dirDeriv_eq_bot_of_eq_top (top_le_iff.1 hx)]
    exact bot_lt_top

/-- If $f \colon \mathbb{R} \to [-\infty, +\infty]$ is proper, then $f'_-(x) > -\infty$ if and only
if some point of $\operatorname{dom} f$ lies strictly to the left of $x$. -/
theorem bot_lt_leftDeriv_iff (hp : ProperConvex f) :
    ⊥ < leftDeriv f x ↔ ∃ z, z < x ∧ f z < ⊤ := by
  rw [leftDeriv_eq_neg_rightDeriv_comp_neg, EReal.lt_neg_comm, EReal.neg_bot,
    rightDeriv_lt_top_iff (f := fun t => f (-t))
      hp.comp_neg]
  exact ⟨fun ⟨z, hz, h⟩ => ⟨-z, by linarith, h⟩,
    fun ⟨z, hz, h⟩ => ⟨-z, by linarith, by simpa using h⟩⟩

/-- Let $f \colon \mathbb{R} \to [-\infty, +\infty]$ be proper and convex. Then
$$f'_-(x) > -\infty \text{ and } f'_+(x) < +\infty \iff x \in
  \operatorname{int}(\operatorname{dom} f).$$

The two halves are usually stated separately: $f'_+ < +\infty$ to the left of the right endpoint
of $\operatorname{dom} f$, and $f'_- > -\infty$ to the right of the left endpoint. On the line,
the two conditions together are interiority. -/
theorem bot_lt_leftDeriv_and_rightDeriv_lt_top_iff (hf : ConvexFn f) (hp : ProperConvex f) :
    (⊥ < leftDeriv f x ∧ rightDeriv f x < ⊤) ↔ x ∈ interior (convexDom f) := by
  rw [bot_lt_leftDeriv_iff hp, rightDeriv_lt_top_iff hp]
  constructor
  · rintro ⟨⟨z₁, hz₁, hfz₁⟩, ⟨z₂, hz₂, hfz₂⟩⟩
    refine mem_interior.2 ⟨Ioo z₁ z₂, fun w hw => ?_, isOpen_Ioo, ⟨hz₁, hz₂⟩⟩
    exact mem_convexDom.2 (hf.lt_top_of_le_of_le hfz₁ hfz₂ hw.1.le hw.2.le)
  · intro hx
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hx)
    have hmem : ∀ w : ℝ, |w - x| < ε → f w < ⊤ := fun w hw =>
      mem_convexDom.1 (interior_subset (hball (by rwa [Metric.mem_ball, Real.dist_eq])))
    exact ⟨⟨x - ε / 2, by linarith, hmem _ (by rw [abs_of_nonpos (by linarith)]; linarith)⟩,
      ⟨x + ε / 2, by linarith, hmem _ (by rw [abs_of_nonneg (by linarith)]; linarith)⟩⟩

/-- If $f \colon \mathbb{R} \to [-\infty, +\infty]$ is proper and convex and
$x \in \operatorname{int}(\operatorname{dom} f)$, then $f'_+(x)$ is real. -/
theorem rightDeriv_finite_of_mem_interior_convexDom (hf : ConvexFn f) (hp : ProperConvex f)
    (hx : x ∈ interior (convexDom f)) : rightDeriv f x ≠ ⊥ ∧ rightDeriv f x ≠ ⊤ := by
  obtain ⟨h1, h2⟩ := (bot_lt_leftDeriv_and_rightDeriv_lt_top_iff hf hp).2 hx
  exact ⟨(h1.trans_le (leftDeriv_le_rightDeriv hf hp x)).ne', h2.ne⟩

/-- If $f \colon \mathbb{R} \to [-\infty, +\infty]$ is proper and convex and
$x \in \operatorname{int}(\operatorname{dom} f)$, then $f'_-(x)$ is real. -/
theorem leftDeriv_finite_of_mem_interior_convexDom (hf : ConvexFn f) (hp : ProperConvex f)
    (hx : x ∈ interior (convexDom f)) : leftDeriv f x ≠ ⊥ ∧ leftDeriv f x ≠ ⊤ := by
  obtain ⟨h1, h2⟩ := (bot_lt_leftDeriv_and_rightDeriv_lt_top_iff hf hp).2 hx
  exact ⟨h1.ne', ((leftDeriv_le_rightDeriv hf hp x).trans_lt h2).ne⟩

end Finite

/-! ### The subdifferential on the line -/

section Subdifferential

variable {f : ℝ → EReal} {x : ℝ}

/-- If $f(x)$ is finite, then $f'_+(x) = f'(x; 1)$. The difference quotients already give $+\infty$
to the right of $\operatorname{dom} f$, so the guard in the definition has no effect. -/
theorem rightDeriv_eq_dirDeriv (hx : f x < ⊤) (hb : f x ≠ ⊥) :
    rightDeriv f x = dirDeriv f x 1 := by
  rcases em (∃ z, x < z ∧ f z < ⊤) with h | h
  · exact rightDeriv_of_exists h
  obtain ⟨p, hp'⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hb hx
  rw [rightDeriv_of_not_exists h]
  refine (top_le_iff.1 (le_dirDeriv fun a ha => ?_)).symm
  have hz : f (x + a • (1 : ℝ)) = ⊤ := by
    rw [show x + a • (1 : ℝ) = x + a by rw [smul_eq_mul]; ring]
    exact top_le_iff.1 (not_lt.1 fun hlt => h ⟨x + a, by linarith, hlt⟩)
  rw [hz, hp', EReal.top_sub_coe,
    EReal.top_div_of_pos_ne_top (by exact_mod_cast ha) (EReal.coe_ne_top a)]

/-- If $f(x)$ is finite, then $f'_-(x) = -f'(x; -1)$. -/
theorem leftDeriv_eq_neg_dirDeriv (hx : f x < ⊤) (hb : f x ≠ ⊥) :
    leftDeriv f x = -dirDeriv f x (-1) := by
  rw [leftDeriv_eq_neg_rightDeriv_comp_neg, rightDeriv_eq_dirDeriv (by simpa using hx)
    (by simpa using hb), dirDeriv_comp_neg]

/-- Let $f \colon \mathbb{R} \to [-\infty, +\infty]$ be finite at $x$. Then for every
$y \in \mathbb{R}$,
$$y \in \partial f(x) \iff f'_-(x) \le y \le f'_+(x).$$

No convexity is needed. The result follows from the description of $\partial f(x)$ by
$f'(x; \cdot)$. Only the directions $+1$ and $-1$ carry information, because $f'(x; \cdot)$ is
positively homogeneous. The subgradients are taken for the pairing `innerₗ ℝ`, which is
multiplication. -/
theorem mem_subdifferential_iff_le_rightDeriv_of_lt_top (hx : f x < ⊤) (hb : f x ≠ ⊥) {y : ℝ} :
    y ∈ subdifferential (innerₗ ℝ) f x ↔
      leftDeriv f x ≤ (y : EReal) ∧ (y : EReal) ≤ rightDeriv f x := by
  have hpair : ∀ v : ℝ, (innerₗ ℝ) v y = y * v := fun v => by simp [innerₗ_apply_apply]
  rw [mem_subdifferential_iff_le_dirDeriv hx.ne hb, rightDeriv_eq_dirDeriv hx hb,
    leftDeriv_eq_neg_dirDeriv hx hb]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h1 := h (-1)
      rw [hpair, mul_neg_one] at h1
      have h2 := EReal.neg_le_neg_iff.2 h1
      rwa [← EReal.coe_neg, neg_neg] at h2
    · have h1 := h 1
      rwa [hpair, mul_one] at h1
  · rintro ⟨hl, hr⟩ v
    rw [hpair]
    rcases lt_trichotomy v 0 with hv | rfl | hv
    · have hw : (0 : ℝ) < -v := by linarith
      have hv1 : dirDeriv f x v = ((-v : ℝ) : EReal) * dirDeriv f x (-1) := by
        have hph := posHomogeneous_dirDeriv f x (-v) hw (-1)
        rwa [show (-v) • (-1 : ℝ) = v by rw [smul_eq_mul]; ring] at hph
      have hy : ((y * v : ℝ) : EReal) = ((-v : ℝ) : EReal) * ((-y : ℝ) : EReal) := by
        rw [← EReal.coe_mul]; congr 1; ring
      rw [hv1, hy, EReal.coe_mul_le_coe_mul_iff hw, EReal.coe_neg]
      have h2 := EReal.neg_le_neg_iff.2 hl
      rwa [neg_neg] at h2
    · rw [dirDeriv_zero hx.ne hb]
      simp
    · have hv1 : dirDeriv f x v = ((v : ℝ) : EReal) * dirDeriv f x 1 := by
        have hph := posHomogeneous_dirDeriv f x v hv 1
        rwa [smul_eq_mul, mul_one] at hph
      have hy : ((y * v : ℝ) : EReal) = ((v : ℝ) : EReal) * ((y : ℝ) : EReal) := by
        rw [← EReal.coe_mul]; congr 1; ring
      rw [hv1, hy, EReal.coe_mul_le_coe_mul_iff hv]
      exact hr

/-- If $f$ is proper and $f'_-(x) \le y \le f'_+(x)$ for a real $y$, then $f(x) < +\infty$. Outside
$\operatorname{dom} f$, one of the two one-sided derivatives is $\pm\infty$ on the wrong side. -/
theorem lt_top_of_leftDeriv_le_of_le_rightDeriv (hp : ProperConvex f) {y : ℝ}
    (h₁ : leftDeriv f x ≤ (y : EReal)) (h₂ : (y : EReal) ≤ rightDeriv f x) : f x < ⊤ := by
  by_contra hcon
  have hxt : f x = ⊤ := top_le_iff.1 (not_lt.1 hcon)
  rcases em (∃ z, z < x ∧ f z < ⊤) with hl | hl
  · rw [leftDeriv_eq_top_of_eq_top hxt hl] at h₁
    exact absurd (top_le_iff.1 h₁) (EReal.coe_ne_top y)
  rcases em (∃ z, x < z ∧ f z < ⊤) with hr | hr
  · rw [rightDeriv_eq_bot_of_eq_top hxt hr] at h₂
    exact absurd (le_bot_iff.1 h₂) (EReal.coe_ne_bot y)
  obtain ⟨w, hw⟩ := hp.convexDom_nonempty
  rcases lt_trichotomy w x with h | h | h
  · exact hl ⟨w, h, mem_convexDom.1 hw⟩
  · rw [h] at hw; exact absurd (mem_convexDom.1 hw) (by rw [hxt]; simp)
  · exact hr ⟨w, h, mem_convexDom.1 hw⟩

/-- Let $f \colon \mathbb{R} \to [-\infty, +\infty]$ be proper. Then for all $x, y \in \mathbb{R}$,
$$y \in \partial f(x) \iff f'_-(x) \le y \le f'_+(x).$$
There is no hypothesis on $x$: outside $\operatorname{dom} f$ both sides are false.

The subgradients are taken for the pairing `innerₗ ℝ`, which is multiplication. -/
theorem mem_subdifferential_iff_le_rightDeriv (hp : ProperConvex f) {y : ℝ} :
    y ∈ subdifferential (innerₗ ℝ) f x ↔
      leftDeriv f x ≤ (y : EReal) ∧ (y : EReal) ≤ rightDeriv f x := by
  rcases lt_or_ge (f x) ⊤ with hx | hx
  · exact mem_subdifferential_iff_le_rightDeriv_of_lt_top hx (hp.ne_bot x)
  refine ⟨fun hmem => ?_, fun ⟨h₁, h₂⟩ => ?_⟩
  · rw [subdifferential_eq_empty_of_notMem_convexDom hp (by rwa [mem_convexDom, not_lt])] at hmem
    exact absurd hmem (notMem_empty y)
  · exact absurd (lt_top_of_leftDeriv_le_of_le_rightDeriv hp h₁ h₂) (not_lt.2 hx)

end Subdifferential

/-! ### One-sided limits of the one-sided derivatives -/

section Limits

variable {f : ℝ → EReal} {x : ℝ}

/-- Let $f$ be a closed proper convex function on $\mathbb{R}$, let $x < y$ with $f(y) = q$ real,
and let $\mu \in \mathbb{R}$ satisfy $\mu < f'_+(z)$ for every $z > x$. Then
$$f(x) \le q - \mu (y - x).$$

At each point $z$ between $x$ and $y$, $\mu < f'_+(z)$, and $f'_+(z)$ is at most the slope from
$z$ to $y$. This bounds $f(z)$ from above, and closedness carries the bound to the endpoint $x$. -/
theorem le_coe_of_lt_rightDeriv (hf : ClosedProperConvexFn f) {y : ℝ} (hxy : x < y) {q : ℝ}
    (hq : f y = (q : EReal)) {μ : ℝ} (hμ : ∀ z, x < z → (μ : EReal) < rightDeriv f z) :
    f x ≤ ((q - μ * (y - x) : ℝ) : EReal) := by
  have hydom : y ∈ convexDom f := mem_convexDom.2 (by rw [hq]; exact EReal.coe_lt_top q)
  have hseg := tendsto_along_segment_of_closed_proper hf hydom x
  have hzeq : ∀ t : ℝ, (1 - t) • y + t • x = y + t * (x - y) := by
    intro t; rw [smul_eq_mul, smul_eq_mul]; ring
  have hest : ∀ᶠ t in 𝓝[<] (1 : ℝ),
      f ((1 - t) • y + t • x) ≤ ((q - μ * (t * (y - x)) : ℝ) : EReal) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
      with t ht1 ht0
    have ht1' : t < 1 := ht1
    rw [hzeq t]
    set w : ℝ := y + t * (x - y) with hw
    have hxw : x < w := by rw [hw]; nlinarith
    have hwy : w < y := by rw [hw]; nlinarith
    have hd : (0 : ℝ) < t * (y - x) := by nlinarith
    have hgap : y - w = t * (y - x) := by rw [hw]; ring
    have hlt := hμ w hxw
    rcases lt_or_ge (f w) ⊤ with hfw | hfw
    · obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hf.proper.ne_bot w) hfw
      rw [rightDeriv_eq_dirDeriv hfw (hf.proper.ne_bot w)] at hlt
      have hslope := dirDeriv_one_le_slope hwy hr hq
      rw [hgap] at hslope
      have : (μ : EReal) < (((q - r) / (t * (y - x)) : ℝ) : EReal) := lt_of_lt_of_le hlt hslope
      rw [EReal.coe_lt_coe_iff, lt_div_iff₀ hd] at this
      rw [hr, EReal.coe_le_coe_iff]
      linarith
    · rw [rightDeriv_eq_bot_of_eq_top (top_le_iff.1 hfw)
        ⟨y, hwy, by rw [hq]; exact EReal.coe_lt_top q⟩] at hlt
      exact absurd hlt (by simp)
  have hlim2 : Tendsto (fun t : ℝ => ((q - μ * (t * (y - x)) : ℝ) : EReal)) (𝓝[<] (1 : ℝ))
      (𝓝 (((q - μ * (1 * (y - x)) : ℝ) : EReal))) := by
    have hcont : Continuous fun t : ℝ => ((q - μ * (t * (y - x)) : ℝ) : EReal) :=
      EReal.continuous_coe_iff.2 (by fun_prop)
    exact (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
  have hle := le_of_tendsto_of_tendsto hseg hlim2 hest
  rwa [one_mul] at hle

/-- Right-continuity of $f'_+$. Let $f \colon \mathbb{R} \to [-\infty, +\infty]$ be a closed proper
convex function. Then for every $x \in \mathbb{R}$,
$$\inf_{z > x} f'_+(z) = f'_+(x).$$
Since $f'_+$ is nondecreasing, this is $\lim_{z \downarrow x} f'_+(z) = f'_+(x)$.

Closedness cannot be dropped. Let $f = 1$ at $0$, $f = 0$ on $(0, \infty)$ and $f = +\infty$ on
$(-\infty, 0)$. This $f$ is convex and proper but not closed, and $f'_+$ jumps at $0$. -/
theorem iInf_rightDeriv_Ioi (hf : ClosedProperConvexFn f) (x : ℝ) :
    ⨅ z ∈ Ioi x, rightDeriv f z = rightDeriv f x := by
  refine le_antisymm ?_ (le_iInf₂ fun z hz => monotone_rightDeriv hf.convex hf.proper hz.le)
  rcases em (∃ w, x < w ∧ f w < ⊤) with hex | hex
  swap
  · rw [rightDeriv_of_not_exists hex]; exact le_top
  obtain ⟨w₀, hw₀, hfw₀⟩ := hex
  obtain ⟨q₀, hq₀⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hf.proper.ne_bot w₀) hfw₀
  by_contra hcon
  obtain ⟨μ, hμ₁, hμ₂⟩ := EReal.lt_iff_exists_real_btwn.1 (not_le.1 hcon)
  have hμ : ∀ z, x < z → (μ : EReal) < rightDeriv f z := fun z hz =>
    lt_of_lt_of_le hμ₂ (iInf₂_le z hz)
  have hx : f x < ⊤ :=
    lt_of_le_of_lt (le_coe_of_lt_rightDeriv hf hw₀ hq₀ hμ) (EReal.coe_lt_top _)
  obtain ⟨p, hp⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hf.proper.ne_bot x) hx
  refine absurd hμ₁ (not_lt.2 ?_)
  rw [rightDeriv_eq_dirDeriv hx (hf.proper.ne_bot x)]
  refine le_dirDeriv fun a ha => ?_
  rw [show x + a • (1 : ℝ) = x + a by rw [smul_eq_mul]; ring]
  rcases lt_or_ge (f (x + a)) ⊤ with hfa | hfa
  · obtain ⟨q, hq⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hf.proper.ne_bot _) hfa
    have hbound := le_coe_of_lt_rightDeriv hf (by linarith : x < x + a) hq hμ
    rw [hp, EReal.coe_le_coe_iff] at hbound
    rw [hp, hq, ← EReal.coe_sub, ← EReal.coe_div, EReal.coe_le_coe_iff,
      le_div_iff₀ ha]
    nlinarith
  · rw [top_le_iff.1 hfa, hp, EReal.top_sub_coe,
      EReal.top_div_of_pos_ne_top (by exact_mod_cast ha) (EReal.coe_ne_top a)]
    exact le_top

/-- Left-continuity of $f'_-$. Let $f \colon \mathbb{R} \to [-\infty, +\infty]$ be a closed proper
convex function. Then for every $x \in \mathbb{R}$,
$$\sup_{z < x} f'_-(z) = f'_-(x).$$

This is the reflection of `ConvexAnalysis.iInf_rightDeriv_Ioi`. -/
theorem iSup_leftDeriv_Iio (hf : ClosedProperConvexFn f) (x : ℝ) :
    ⨆ z ∈ Iio x, leftDeriv f z = leftDeriv f x := by
  refine le_antisymm (iSup₂_le fun z hz => monotone_leftDeriv hf.convex hf.proper hz.le) ?_
  rw [leftDeriv_eq_neg_rightDeriv_comp_neg, ← iInf_rightDeriv_Ioi hf.comp_neg (-x), EReal.neg_le]
  refine le_iInf₂ fun w hw => ?_
  rw [← neg_neg w, ← neg_neg (rightDeriv _ _), ← leftDeriv_eq_neg_rightDeriv_comp_neg]
  exact EReal.neg_le_neg_iff.2 (le_iSup₂ (f := fun z (_ : z ∈ Iio x) => leftDeriv f z) (-w)
    (show -w < x from neg_lt.2 hw))

/-- Let $f \colon \mathbb{R} \to [-\infty, +\infty]$ be a closed proper convex function. Then for
every $x \in \mathbb{R}$, the left derivative has $f'_+(x)$ as its limit from the right:
$$\inf_{z > x} f'_-(z) = f'_+(x).$$
-/
theorem iInf_leftDeriv_Ioi (hf : ClosedProperConvexFn f) (x : ℝ) :
    ⨅ z ∈ Ioi x, leftDeriv f z = rightDeriv f x := by
  refine le_antisymm ?_ (le_iInf₂ fun z hz => rightDeriv_le_leftDeriv hf.proper hz)
  rw [← iInf_rightDeriv_Ioi hf x]
  exact iInf₂_mono fun z _ => leftDeriv_le_rightDeriv hf.convex hf.proper z

/-- Let $f \colon \mathbb{R} \to [-\infty, +\infty]$ be a closed proper convex function. Then for
every $x \in \mathbb{R}$, the right derivative has $f'_-(x)$ as its limit from the left:
$$\sup_{z < x} f'_+(z) = f'_-(x).$$
-/
theorem iSup_rightDeriv_Iio (hf : ClosedProperConvexFn f) (x : ℝ) :
    ⨆ z ∈ Iio x, rightDeriv f z = leftDeriv f x := by
  refine le_antisymm (iSup₂_le fun z hz => rightDeriv_le_leftDeriv hf.proper hz) ?_
  rw [← iSup_leftDeriv_Iio hf x]
  exact iSup₂_mono fun z _ => leftDeriv_le_rightDeriv hf.convex hf.proper z

/-! ### The four one-sided limits as limits of functions -/

/-- For a closed proper convex $f$ on $\mathbb{R}$, $f'_+(z) \to f'_+(x)$ as $z \downarrow x$. -/
theorem tendsto_rightDeriv_nhdsWithin_Ioi (hf : ClosedProperConvexFn f) (x : ℝ) :
    Tendsto (rightDeriv f) (𝓝[>] x) (𝓝 (rightDeriv f x)) := by
  simpa only [sInf_image, iInf_rightDeriv_Ioi hf x] using
    (monotone_rightDeriv hf.convex hf.proper).tendsto_nhdsGT x

/-- For a closed proper convex $f$ on $\mathbb{R}$, $f'_+(z) \to f'_-(x)$ as $z \uparrow x$. -/
theorem tendsto_rightDeriv_nhdsWithin_Iio (hf : ClosedProperConvexFn f) (x : ℝ) :
    Tendsto (rightDeriv f) (𝓝[<] x) (𝓝 (leftDeriv f x)) := by
  simpa only [sSup_image, iSup_rightDeriv_Iio hf x] using
    (monotone_rightDeriv hf.convex hf.proper).tendsto_nhdsLT x

/-- For a closed proper convex $f$ on $\mathbb{R}$, $f'_-(z) \to f'_+(x)$ as $z \downarrow x$. -/
theorem tendsto_leftDeriv_nhdsWithin_Ioi (hf : ClosedProperConvexFn f) (x : ℝ) :
    Tendsto (leftDeriv f) (𝓝[>] x) (𝓝 (rightDeriv f x)) := by
  simpa only [sInf_image, iInf_leftDeriv_Ioi hf x] using
    (monotone_leftDeriv hf.convex hf.proper).tendsto_nhdsGT x

/-- For a closed proper convex $f$ on $\mathbb{R}$, $f'_-(z) \to f'_-(x)$ as $z \uparrow x$. -/
theorem tendsto_leftDeriv_nhdsWithin_Iio (hf : ClosedProperConvexFn f) (x : ℝ) :
    Tendsto (leftDeriv f) (𝓝[<] x) (𝓝 (leftDeriv f x)) := by
  simpa only [sSup_image, iSup_leftDeriv_Iio hf x] using
    (monotone_leftDeriv hf.convex hf.proper).tendsto_nhdsLT x

end Limits

/-! ### A nondecreasing function between the two derivatives -/

section Determination

variable {f g : ℝ → EReal}

/-- If $f$ is proper and $f'_- \le \varphi \le f'_+$ on $\mathbb{R}$, then $\varphi$ is
nondecreasing. This follows from $f'_+(y) \le f'_-(z)$ for $y < z$. -/
theorem monotone_of_leftDeriv_le_of_le_rightDeriv (hp : ProperConvex f) {φ : ℝ → EReal}
    (h₁ : ∀ z, leftDeriv f z ≤ φ z) (h₂ : ∀ z, φ z ≤ rightDeriv f z) : Monotone φ := by
  intro y z hyz
  rcases eq_or_lt_of_le hyz with rfl | hlt
  · exact le_rfl
  exact (h₂ y).trans ((rightDeriv_le_leftDeriv hp hlt).trans (h₁ z))

/-- If $f$ is closed, proper and convex on $\mathbb{R}$ and $f'_- \le \varphi \le f'_+$, then
$\inf_{z > x} \varphi(z) = f'_+(x)$ for every $x$. So $\varphi$ determines $f'_+$. -/
theorem iInf_Ioi_eq_rightDeriv (hf : ClosedProperConvexFn f) {φ : ℝ → EReal}
    (h₁ : ∀ z, leftDeriv f z ≤ φ z) (h₂ : ∀ z, φ z ≤ rightDeriv f z) (x : ℝ) :
    ⨅ z ∈ Ioi x, φ z = rightDeriv f x := by
  refine le_antisymm ?_ ?_
  · rw [← iInf_rightDeriv_Ioi hf x]
    exact iInf₂_mono fun z _ => h₂ z
  · rw [← iInf_leftDeriv_Ioi hf x]
    exact iInf₂_mono fun z _ => h₁ z

/-- If $f$ is closed, proper and convex on $\mathbb{R}$ and $f'_- \le \varphi \le f'_+$, then
$\sup_{z < x} \varphi(z) = f'_-(x)$ for every $x$. So $\varphi$ determines $f'_-$. -/
theorem iSup_Iio_eq_leftDeriv (hf : ClosedProperConvexFn f) {φ : ℝ → EReal}
    (h₁ : ∀ z, leftDeriv f z ≤ φ z) (h₂ : ∀ z, φ z ≤ rightDeriv f z) (x : ℝ) :
    ⨆ z ∈ Iio x, φ z = leftDeriv f x := by
  refine le_antisymm ?_ ?_
  · rw [← iSup_rightDeriv_Iio hf x]
    exact iSup₂_mono fun z _ => h₂ z
  · rw [← iSup_leftDeriv_Iio hf x]
    exact iSup₂_mono fun z _ => h₁ z

/-- Two proper functions $f, g$ on $\mathbb{R}$ with $f'_+ = g'_+$ and $f'_- = g'_-$ have the same
subdifferential, because the subdifferential is the interval between the one-sided derivatives. -/
theorem subgradientRel_eq_of_deriv_eq (hpf : ProperConvex f) (hpg : ProperConvex g)
    (hr : ∀ x, rightDeriv f x = rightDeriv g x) (hl : ∀ x, leftDeriv f x = leftDeriv g x) :
    subgradientRel (innerₗ ℝ) f = subgradientRel (innerₗ ℝ) g := by
  ext p
  change p.2 ∈ subdifferential (innerₗ ℝ) f p.1 ↔ p.2 ∈ subdifferential (innerₗ ℝ) g p.1
  rw [mem_subdifferential_iff_le_rightDeriv hpf, mem_subdifferential_iff_le_rightDeriv hpg, hr, hl]

/-- Two closed proper convex functions $f, g$ on $\mathbb{R}$ with $f'_+ = g'_+$ and $f'_- = g'_-$
differ by a constant: $g = f + \alpha$ for some $\alpha \in \mathbb{R}$. -/
theorem exists_eq_add_coe_of_deriv_eq (hf : ClosedProperConvexFn f) (hg : ClosedProperConvexFn g)
    (hr : ∀ x, rightDeriv f x = rightDeriv g x) (hl : ∀ x, leftDeriv f x = leftDeriv g x) :
    ∃ α : ℝ, ∀ x, g x = f x + (α : EReal) := by
  have : IsCompatiblePairing ((innerₗ ℝ).flip) := by rw [flip_innerₗ]; infer_instance
  exact eq_add_coe_of_subgradientRel_subset hf hg
    (subgradientRel_eq_of_deriv_eq hf.proper hg.proper hr hl).subset

/-- Let $f, g \colon \mathbb{R} \to [-\infty, +\infty]$ be closed proper convex functions, and let
$\varphi \colon \mathbb{R} \to [-\infty, +\infty]$ satisfy
$$f'_- \le \varphi \le f'_+ \quad \text{and} \quad g'_- \le \varphi \le g'_+.$$
Then there is $\alpha \in \mathbb{R}$ with $g = f + \alpha$. This is the uniqueness part of
Theorem 24.2 of [rockafellar1970convex].

The existence part is `ConvexAnalysis.exists_closedProperConvexFn_forall_le_le`. -/
theorem exists_eq_add_coe_of_le_le (hf : ClosedProperConvexFn f) (hg : ClosedProperConvexFn g)
    {φ : ℝ → EReal} (hf₁ : ∀ z, leftDeriv f z ≤ φ z) (hf₂ : ∀ z, φ z ≤ rightDeriv f z)
    (hg₁ : ∀ z, leftDeriv g z ≤ φ z) (hg₂ : ∀ z, φ z ≤ rightDeriv g z) :
    ∃ α : ℝ, ∀ x, g x = f x + (α : EReal) :=
  exists_eq_add_coe_of_deriv_eq hf hg
    (fun x => by rw [← iInf_Ioi_eq_rightDeriv hf hf₁ hf₂ x, iInf_Ioi_eq_rightDeriv hg hg₁ hg₂ x])
    (fun x => by rw [← iSup_Iio_eq_leftDeriv hf hf₁ hf₂ x, iSup_Iio_eq_leftDeriv hg hg₁ hg₂ x])

end Determination

/-! ### Cycles as lists, and rotation -/

section Cycle

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ}

/-- The **telescoping sum around a cycle** given as a list of pairs: for the list
$(x_0, y_0), (x_1, y_1), \dots, (x_m, y_m)$, it is
$$\langle x_1 - x_0, y_0 \rangle + \dots + \langle x_m - x_{m-1}, y_{m-1} \rangle + \langle
  x_0 - x_m, y_m \rangle,$$
that is, `ConvexAnalysis.chainVal` with the head of the list as both the start and the free
endpoint. The empty cycle has the sum $0$. -/
def cycleVal (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : List (E × F) → ℝ
  | [] => 0
  | p :: l => chainVal B p l p.1

/-- The empty cycle has the sum $0$. -/
@[simp] theorem cycleVal_nil : cycleVal B [] = 0 := rfl

/-- A cycle with one pair has the sum $0$. -/
@[simp] theorem cycleVal_singleton (p : E × F) : cycleVal B [p] = 0 := by
  simp [cycleVal]

/-- A multivalued mapping $\rho$ is cyclically monotone if and only if every list of pairs in $\rho$
has a cycle sum (`ConvexAnalysis.cycleVal`) that is at most $0$. -/
theorem isCyclicallyMonotone_iff_cycleVal (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (ρ : SetRel E F) :
    IsCyclicallyMonotone B ρ ↔ ∀ L : List (E × F), (∀ q ∈ L, q ∈ ρ) → cycleVal B L ≤ 0 := by
  constructor
  · intro h L hL
    match L with
    | [] => simp
    | p :: l => exact h p (hL p (by simp)) l fun q hq => hL q (by simp [hq])
  · intro h s hs l hl
    exact h (s :: l) fun q hq => by
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hs
      · exact hl q hq

/-- A rotation of a cycle by one step does not change its sum: the cycle sum of $p, l$ equals the
cycle sum of $l, p$. -/
theorem cycleVal_cons (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (p : E × F) (l : List (E × F)) :
    cycleVal B (p :: l) = cycleVal B (l ++ [p]) := by
  match l with
  | [] => simp
  | q :: l' =>
    change chainVal B p (q :: l') p.1 = chainVal B q (l' ++ [p]) q.1
    rw [chainVal_cons, chainVal_append_singleton]
    ring

/-- An arbitrary rotation of a cycle does not change its sum: the cycle sum of the list $A$ followed
by the list $C$ equals the cycle sum of $C$ followed by $A$. -/
theorem cycleVal_append_comm (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (A C : List (E × F)) :
    cycleVal B (A ++ C) = cycleVal B (C ++ A) := by
  induction A generalizing C with
  | nil => simp
  | cons a A' ih =>
    calc cycleVal B ((a :: A') ++ C)
        = cycleVal B (a :: (A' ++ C)) := by rw [List.cons_append]
      _ = cycleVal B ((A' ++ C) ++ [a]) := cycleVal_cons B a _
      _ = cycleVal B (A' ++ (C ++ [a])) := by rw [List.append_assoc]
      _ = cycleVal B ((C ++ [a]) ++ A') := ih _
      _ = cycleVal B (C ++ ([a] ++ A')) := by rw [List.append_assoc]
      _ = cycleVal B (C ++ (a :: A')) := by rw [List.singleton_append]

/-- A telescoping sum is affine in its free endpoint, with the slope given by a pair of the chain:
there are a pair $r$ in the list $s, l$ and $c \in \mathbb{R}$ with $\operatorname{chainVal}(s,
l, x) = \langle x, r_2 \rangle - c$ for every $x$. This sharpens
`ConvexAnalysis.exists_chainVal_eq`. -/
theorem exists_chainVal_eq_mem (l : List (E × F)) (s : E × F) :
    ∃ (r : E × F) (c : ℝ), r ∈ s :: l ∧ ∀ x, chainVal B s l x = B x r.2 - c := by
  induction l generalizing s with
  | nil => exact ⟨s, B s.1 s.2, by simp, fun x => by rw [chainVal_nil, map_sub,
      LinearMap.sub_apply]⟩
  | cons q l ih =>
    obtain ⟨r, c, hmem, h⟩ := ih q
    refine ⟨r, c - B (q.1 - s.1) s.2, ?_, fun x => ?_⟩
    · rcases List.mem_cons.1 hmem with rfl | hmem
      · simp
      · simp [hmem]
    · rw [chainVal_cons, h x]; ring

/-- Deletion of the head of a cycle changes its sum by one product: for pairs $p, q$ and a list $l$,
there is a pair $r$ in the list $q, l$ with
$$\operatorname{cycleVal}(p, q, l) = \operatorname{cycleVal}(q, l) + \langle q_1 - p_1, p_2 -
  r_2 \rangle.$$
If the head $p$ dominates the rest of the cycle in both coordinates, the product is at most $0$
on the line. -/
theorem exists_cycleVal_cons_eq (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (p q : E × F) (l : List (E × F)) :
    ∃ r ∈ q :: l, cycleVal B (p :: q :: l)
      = cycleVal B (q :: l) + B (q.1 - p.1) (p.2 - r.2) := by
  obtain ⟨r, c, hmem, h⟩ := exists_chainVal_eq_mem (B := B) l q
  refine ⟨r, hmem, ?_⟩
  change chainVal B p (q :: l) p.1 = chainVal B q l q.1 + B (q.1 - p.1) (p.2 - r.2)
  rw [chainVal_cons, h p.1, h q.1]
  simp only [map_sub, LinearMap.sub_apply]
  ring

end Cycle

/-! ### Monotone relations on the line -/

section Line

variable {ρ : SetRel ℝ ℝ} {f : ℝ → EReal}

/-- The pairing `innerₗ ℝ` of the line with itself is multiplication: $\langle a, b \rangle = ab$.
-/
theorem innerₗ_real_apply (a b : ℝ) : (innerₗ ℝ) a b = a * b := by
  simp [innerₗ_apply_apply, mul_comm]

/-- Every nonempty finite list attains the maximum of a real-valued function $g$ on its elements:
there is $a$ in the list with $g(b) \le g(a)$ for every $b$ in the list. -/
theorem exists_max_mem_of_ne_nil {α : Type*} (g : α → ℝ) :
    ∀ l : List α, l ≠ [] → ∃ a ∈ l, ∀ b ∈ l, g b ≤ g a := by
  intro l
  induction l with
  | nil => exact fun h => absurd rfl h
  | cons a t ih =>
    intro _
    rcases eq_or_ne t [] with rfl | ht
    · exact ⟨a, by simp, by simp⟩
    obtain ⟨c, hc, hmax⟩ := ih ht
    rcases le_total (g c) (g a) with h | h
    · refine ⟨a, by simp, fun b hb => ?_⟩
      rcases List.mem_cons.1 hb with rfl | hb
      · exact le_rfl
      · exact (hmax b hb).trans h
    · refine ⟨c, by simp [hc], fun b hb => ?_⟩
      rcases List.mem_cons.1 hb with rfl | hb
      · exact h
      · exact hmax b hb

/-- On the line, a relation $\rho \subseteq \mathbb{R} \times \mathbb{R}$ is monotone if and only if
any two of its pairs are comparable in the coordinatewise order: $p \le q$ or $q \le p$. So a
monotone relation is a non-decreasing curve. -/
theorem isMonotoneRel_iff_forall_le_or_le :
    IsMonotoneRel (innerₗ ℝ) ρ ↔ ∀ p ∈ ρ, ∀ q ∈ ρ, p ≤ q ∨ q ≤ p := by
  constructor
  · intro h p hp q hq
    have hnn := h p hp q hq
    rw [innerₗ_real_apply] at hnn
    rcases mul_nonneg_iff.1 hnn with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inr (Prod.le_def.2 ⟨by linarith, by linarith⟩)
    · exact Or.inl (Prod.le_def.2 ⟨by linarith, by linarith⟩)
  · intro h p hp q hq
    rw [innerₗ_real_apply]
    rcases h p hp q hq with hle | hle
    · rw [Prod.le_def] at hle
      nlinarith [hle.1, hle.2]
    · rw [Prod.le_def] at hle
      nlinarith [hle.1, hle.2]

/-- Let $M \in \mathbb{R} \times \mathbb{R}$ dominate every pair $q$ of the list $L$ in both
coordinates. Then the deletion of $M$ from the head of the cycle $M, L$ does not decrease the
cycle sum:
$$\operatorname{cycleVal}(M, L) \le \operatorname{cycleVal}(L).$$
The deleted edge runs backwards in the first coordinate and forwards in the second. -/
theorem cycleVal_cons_le_cycleVal {M : ℝ × ℝ} {L : List (ℝ × ℝ)}
    (hdom : ∀ q ∈ L, q.1 ≤ M.1 ∧ q.2 ≤ M.2) :
    cycleVal (innerₗ ℝ) (M :: L) ≤ cycleVal (innerₗ ℝ) L := by
  match L with
  | [] => simp
  | q :: l =>
    obtain ⟨r, hr, heq⟩ := exists_cycleVal_cons_eq (innerₗ ℝ) M q l
    rw [heq, innerₗ_real_apply]
    have h₁ : q.1 - M.1 ≤ 0 := sub_nonpos.2 (hdom q (by simp)).1
    have h₂ : 0 ≤ M.2 - r.2 := sub_nonneg.2 (hdom r hr).2
    nlinarith

/-- On the line, every monotone relation $\rho \subseteq \mathbb{R} \times \mathbb{R}$ is cyclically
monotone.

A cycle can be rotated so that the pair with the largest sum $x + y$ comes first. Monotonicity
makes this pair dominate the whole cycle in both coordinates, so its deletion does not decrease
the sum. Induction on the length completes the proof. In higher dimensions the result is false:
cyclic monotonicity is strictly stronger than monotonicity. -/
theorem IsMonotoneRel.isCyclicallyMonotone (h : IsMonotoneRel (innerₗ ℝ) ρ) :
    IsCyclicallyMonotone (innerₗ ℝ) ρ := by
  rw [isCyclicallyMonotone_iff_cycleVal]
  have hord := isMonotoneRel_iff_forall_le_or_le.1 h
  suffices H : ∀ n (L : List (ℝ × ℝ)), L.length ≤ n → (∀ q ∈ L, q ∈ ρ) →
      cycleVal (innerₗ ℝ) L ≤ 0 from fun L hL => H L.length L le_rfl hL
  intro n
  induction n with
  | zero =>
    intro L hlen _
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hlen)]
    simp
  | succ n ih =>
    intro L hlen hL
    rcases eq_or_ne L [] with rfl | hne
    · simp
    obtain ⟨M, hM, hmax⟩ := exists_max_mem_of_ne_nil (fun p : ℝ × ℝ => p.1 + p.2) L hne
    have hdom : ∀ q ∈ L, q.1 ≤ M.1 ∧ q.2 ≤ M.2 := by
      intro q hq
      have hsum : q.1 + q.2 ≤ M.1 + M.2 := hmax q hq
      rcases hord q (hL q hq) M (hL M hM) with hle | hle
      · exact Prod.le_def.1 hle
      · rw [Prod.le_def] at hle
        exact ⟨by linarith [hle.1, hle.2], by linarith [hle.1, hle.2]⟩
    obtain ⟨A, T, rfl⟩ := List.append_of_mem hM
    have hmem : ∀ q ∈ T ++ A, q ∈ A ++ M :: T := by
      intro q hq
      rcases List.mem_append.1 hq with hq | hq
      · exact List.mem_append.2 (Or.inr (List.mem_cons_of_mem M hq))
      · exact List.mem_append.2 (Or.inl hq)
    have hlen' : (T ++ A).length ≤ n := by
      simp only [List.length_append, List.length_cons] at hlen ⊢
      omega
    rw [cycleVal_append_comm, List.cons_append]
    exact (cycleVal_cons_le_cycleVal fun q hq => hdom q (hmem q hq)).trans
      (ih (T ++ A) hlen' fun q hq => hL q (hmem q hq))

/-- On the line, a relation is maximal monotone if and only if it is maximal cyclically monotone,
because the two notions of monotonicity agree. -/
theorem isMaximalMonotoneRel_iff_isMaximalCyclicallyMonotone :
    IsMaximalMonotoneRel (innerₗ ℝ) ρ ↔ IsMaximalCyclicallyMonotone (innerₗ ℝ) ρ := by
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁.isCyclicallyMonotone, fun σ hσ hsub => h₂ σ hσ.isMonotoneRel hsub⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁.isMonotoneRel, fun σ hσ hsub => h₂ σ hσ.isCyclicallyMonotone hsub⟩

/-- A relation $\rho \subseteq \mathbb{R} \times \mathbb{R}$ is maximal monotone if and only if
$$\rho = \partial f \text{ for some closed proper convex } f \colon \mathbb{R} \to [-\infty,
  +\infty].$$
This is Theorem 24.3 of [rockafellar1970convex].

The maximal monotone relations on the line are the maximal chains for the coordinatewise order,
the complete non-decreasing curves. With `ConvexAnalysis.mem_subgradientRel_iff`, a complete
non-decreasing curve is always the region $f'_-(x) \le y \le f'_+(x)$ between the two one-sided
derivatives of a closed proper convex function, and conversely. Here $\partial f$ is the graph
`ConvexAnalysis.subgradientRel (innerₗ ℝ) f`. -/
theorem isMaximalMonotoneRel_iff_exists_closedProperConvexFn :
    IsMaximalMonotoneRel (innerₗ ℝ) ρ ↔
      ∃ f : ℝ → EReal, ClosedProperConvexFn f ∧ ρ = subgradientRel (innerₗ ℝ) f := by
  have : IsCompatiblePairing ((innerₗ ℝ).flip) := by rw [flip_innerₗ]; infer_instance
  rw [isMaximalMonotoneRel_iff_isMaximalCyclicallyMonotone,
    isMaximalCyclicallyMonotone_iff_exists_closedProperConvexFn]

/-- If $f \colon \mathbb{R} \to [-\infty, +\infty]$ is proper, then $(x, y)$ is in the graph of
$\partial f$ if and only if $f'_-(x) \le y \le f'_+(x)$. -/
theorem mem_subgradientRel_iff (hp : ProperConvex f) {x y : ℝ} :
    ((x, y) : ℝ × ℝ) ∈ subgradientRel (innerₗ ℝ) f ↔
      leftDeriv f x ≤ (y : EReal) ∧ (y : EReal) ≤ rightDeriv f x :=
  mem_subdifferential_iff_le_rightDeriv hp

end Line

end ConvexAnalysis
