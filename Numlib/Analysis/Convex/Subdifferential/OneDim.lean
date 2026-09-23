import Numlib.Analysis.Convex.Closure
import Numlib.Analysis.Convex.Operations.Closed
import Numlib.Analysis.Convex.Subdifferential.Monotone

/-!
# One-sided derivatives of a convex function on the line

On the line a convex function has a right derivative `f'₊` and a left derivative `f'₋` at every
point, with values in `[-∞, +∞]`, and they carry all the first-order information:
`∂f(x) = {x* ∈ ℝ | f'₋(x) ≤ x* ≤ f'₊(x)}`. Both are nondecreasing, interlaced as
`f'₊(z₁) ≤ f'₋(x) ≤ f'₊(x) ≤ f'₋(z₂)` for `z₁ < x < z₂`, and both are real exactly on
`int (dom f)`. When `f` is closed each is the one-sided limit of the other — `f'₊(z)` and `f'₋(z)`
both tend to `f'₊(x)` as `z ↓ x`, and to `f'₋(x)` as `z ↑ x` — so `f'₊` is right-continuous, `f'₋`
is left-continuous, and either determines the other. Hence any nondecreasing `φ` with
`f'₋ ≤ φ ≤ f'₊` determines `∂f`, and so determines `f` up to a constant.

One dimension also collapses the two monotonicity notions of `Subdifferential/Monotone.lean` into
one. A monotone relation on `ℝ` is exactly a set totally ordered by the coordinatewise order of
`ℝ × ℝ`, a *non-decreasing curve*, and any cycle through such a set may be rotated to start at its
largest pair, which dominates the cycle in both coordinates and may therefore be deleted without
decreasing the telescoping sum. So monotone and cyclically monotone agree on the line, and the
maximal monotone relations — the *complete non-decreasing curves* — are precisely the graphs of the
subdifferentials of the closed proper convex functions.

## Main definitions

* `rightDeriv f x`, `leftDeriv f x` — the two one-sided derivatives, extended by `+∞` to the right
  of `dom f` and by `-∞` to its left.
* `cycleVal B L` — the telescoping sum around a cycle presented as a single list of pairs, the form
  in which rotation invariance is expressible.

## Main results

* `mem_subdifferential_iff_le_rightDeriv` — `∂f(x)` is the interval `[f'₋(x), f'₊(x)]`.
* `iInf_rightDeriv_Ioi`, `iSup_leftDeriv_Iio`, `iInf_leftDeriv_Ioi`, `iSup_rightDeriv_Iio` and
  their `Tendsto` forms — the four limit formulas, for a closed proper convex `f`.
* `exists_eq_add_coe_of_le_le` — two closed proper convex functions squeezed around a common `φ`
  differ by a constant.
* `IsMonotoneRel.isCyclicallyMonotone` — on the line the two monotonicity notions coincide.
* `isMaximalMonotoneRel_iff_exists_closedProperConvexFn` — the maximal monotone relations on the
  line are exactly the subdifferentials of closed proper convex functions
  ([rockafellar1970convex] Theorem 24.3).

## Implementation notes

`f'₊` is `f'(x; 1)` and `f'₋` is `-f'(x; -1)`, so the whole theory of `dirDeriv` is available and
nothing is redefined. Both are *guarded*: `f'₊(x)` is `f'(x; 1)` provided some point of `dom f`
lies to the right of `x`, and `+∞` otherwise. The guard is needed because where `f x = ⊤` every
difference quotient is `⊤ - ⊤ = ⊥`, so the unguarded infimum would be `-∞` on *both* sides of
`dom f`, and the two sides must be told apart. Where `f` is finite the guard is inert.

The two sides are exchanged by the reflection `t ↦ -t`: `leftDeriv_eq_neg_rightDeriv_comp_neg`
states `f'₋(x) = -(f ∘ neg)'₊(-x)`, and the left-hand results are derived from their right-hand
twins through it rather than proved again. The one-sided limits of a monotone function are
Mathlib's `Monotone.tendsto_nhdsGT` and `Monotone.tendsto_nhdsLT`.

## References

* [rockafellar1970convex] §23 and §24.
-/

open Set Filter Topology

namespace ConvexAnalysis

/-! ### The directional derivative at a point outside the effective domain -/

section Outside

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {f : E → EReal} {x : E}

/-- Where `f` is `+∞` every difference quotient is `-∞`, so the directional derivative is `-∞` in
every direction. This is the value wanted to the *left* of `dom f` and the one
overrides to the right. -/
theorem dirDeriv_eq_bot_of_eq_top (hx : f x = ⊤) (y : E) : dirDeriv f x y = ⊥ := by
  refine le_antisymm ?_ bot_le
  refine (dirDeriv_le f x y one_pos).trans ?_
  rw [hx, EReal.sub_top,
    EReal.bot_div_of_pos_ne_top (by exact_mod_cast one_pos) (EReal.coe_ne_top 1)]

end Outside

/-! ### The right and left derivatives -/

section Defs

variable {f : ℝ → EReal} {x : ℝ}

/-- The **right derivative** of an extended-real-valued function on the line,

```
f'₊(x) = lim_{z ↓ x} (f z - f x) / (z - x),
```

with the convention that it is `+∞` at every point lying to the right of `dom f`. Without that
override the difference quotients would all be `-∞` there, which is the value belonging to the
points on the *left*. -/
noncomputable def rightDeriv (f : ℝ → EReal) (x : ℝ) : EReal :=
  ⨅ _ : ∃ z, x < z ∧ f z < ⊤, dirDeriv f x 1

/-- The **left derivative**

```
f'₋(x) = lim_{z ↑ x} (f z - f x) / (z - x),
```

`-∞` at every point lying to the left of `dom f`. It is `-f'(x; -1)` because the increment
`z - x` is negative. -/
noncomputable def leftDeriv (f : ℝ → EReal) (x : ℝ) : EReal :=
  ⨆ _ : ∃ z, z < x ∧ f z < ⊤, -dirDeriv f x (-1)

theorem rightDeriv_of_exists (h : ∃ z, x < z ∧ f z < ⊤) :
    rightDeriv f x = dirDeriv f x 1 := iInf_pos h

theorem rightDeriv_of_not_exists (h : ¬∃ z, x < z ∧ f z < ⊤) : rightDeriv f x = ⊤ := iInf_neg h

theorem leftDeriv_of_exists (h : ∃ z, z < x ∧ f z < ⊤) :
    leftDeriv f x = -dirDeriv f x (-1) := iSup_pos h

theorem leftDeriv_of_not_exists (h : ¬∃ z, z < x ∧ f z < ⊤) : leftDeriv f x = ⊥ := iSup_neg h

/-- To the right of `dom f` the right derivative is `+∞` by fiat; to the left of it, `-∞`. -/
theorem rightDeriv_eq_bot_of_eq_top (hx : f x = ⊤) (h : ∃ z, x < z ∧ f z < ⊤) :
    rightDeriv f x = ⊥ := by
  rw [rightDeriv_of_exists h, dirDeriv_eq_bot_of_eq_top hx]

/-- To the left of `dom f` the left derivative is `-∞` by fiat; to the right of it, `+∞`. -/
theorem leftDeriv_eq_top_of_eq_top (hx : f x = ⊤) (h : ∃ z, z < x ∧ f z < ⊤) :
    leftDeriv f x = ⊤ := by
  rw [leftDeriv_of_exists h, dirDeriv_eq_bot_of_eq_top hx, EReal.neg_bot]

end Defs

/-! ### Reflection

The reflection `t ↦ -t` exchanges the two sides: `f'₋(x) = -(f ∘ neg)'₊(-x)`. The statements about
`f'₋` below are proved this way from their twins about `f'₊`; the reflected function is again
closed, proper and convex. -/

section Reflection

section General

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {f : E → EReal}

/-- Reflecting the function reflects the base point and the direction of `f'(x; v)`. -/
theorem dirDeriv_comp_neg (f : E → EReal) (x v : E) :
    dirDeriv (fun t => f (-t)) (-x) v = dirDeriv f x (-v) := by
  simp only [dirDeriv_apply, smul_neg, neg_add_rev, neg_neg, add_comm]

end General

variable {f : ℝ → EReal} {x : ℝ}

/-- **The left derivative is the reflected right derivative**: `f'₋(x) = -(f ∘ neg)'₊(-x)`, guard
included. -/
theorem leftDeriv_eq_neg_rightDeriv_comp_neg (f : ℝ → EReal) (x : ℝ) :
    leftDeriv f x = -rightDeriv (fun t => f (-t)) (-x) := by
  have hex : (∃ z, -x < z ∧ f (-z) < ⊤) ↔ ∃ z, z < x ∧ f z < ⊤ :=
    ⟨fun ⟨z, hz, h⟩ => ⟨-z, by linarith, h⟩,
      fun ⟨z, hz, h⟩ => ⟨-z, by linarith, by simpa using h⟩⟩
  by_cases h : ∃ z, z < x ∧ f z < ⊤
  · rw [leftDeriv_of_exists h, rightDeriv_of_exists (hex.2 h), dirDeriv_comp_neg]
  · rw [leftDeriv_of_not_exists h, rightDeriv_of_not_exists (mt hex.1 h), EReal.neg_top]

/-- The same reflection read the other way: `f'₊(x) = -(f ∘ neg)'₋(-x)`. -/
theorem rightDeriv_eq_neg_leftDeriv_comp_neg (f : ℝ → EReal) (x : ℝ) :
    rightDeriv f x = -leftDeriv (fun t => f (-t)) (-x) := by
  simp [leftDeriv_eq_neg_rightDeriv_comp_neg]

end Reflection

/-! ### Monotonicity -/

section Order

variable {f : ℝ → EReal} {x : ℝ}

/-- On the line, the effective domain of a convex function is an interval: a point between two
points of `dom f` lies in `dom f`. -/
theorem ConvexFn.lt_top_of_le_of_le (hf : ConvexFn f) {z₁ z₂ : ℝ} (h₁ : f z₁ < ⊤) (h₂ : f z₂ < ⊤)
    (hz₁ : z₁ ≤ x) (hz₂ : x ≤ z₂) : f x < ⊤ :=
  hf.convex_convexDom.ordConnected.out (mem_convexDom.2 h₁) (mem_convexDom.2 h₂)
      (mem_Icc.2 ⟨hz₁, hz₂⟩)

theorem dirDeriv_le_rightDeriv (f : ℝ → EReal) (x : ℝ) :
    dirDeriv f x 1 ≤ rightDeriv f x := by
  rcases em (∃ z, x < z ∧ f z < ⊤) with h | h
  · exact le_of_eq (rightDeriv_of_exists h).symm
  · rw [rightDeriv_of_not_exists h]; exact le_top

theorem leftDeriv_le_neg_dirDeriv (f : ℝ → EReal) (x : ℝ) :
    leftDeriv f x ≤ -dirDeriv f x (-1) := by
  rw [leftDeriv_eq_neg_rightDeriv_comp_neg, EReal.neg_le_neg_iff, ← dirDeriv_comp_neg]
  exact dirDeriv_le_rightDeriv _ _

/-- `f'₋(x) ≤ f'₊(x)` at every point of the line. -/
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

/-- The right derivative at the left end of an interval is at most the slope across it. This is
one instance of the defining infimum, with the step `z - y`. -/
theorem dirDeriv_one_le_slope {y z p q : ℝ} (hyz : y < z) (hfy : f y = (p : EReal))
    (hfz : f z = (q : EReal)) : dirDeriv f y 1 ≤ (((q - p) / (z - y) : ℝ) : EReal) := by
  have hle := dirDeriv_le f y 1 (by linarith : (0 : ℝ) < z - y)
  rwa [show y + (z - y) • (1 : ℝ) = z by rw [smul_eq_mul]; ring, hfy, hfz,
    ← EReal.coe_sub, ← EReal.coe_div] at hle

/-- The mirror image of `dirDeriv_one_le_slope`, at the right end of the interval. -/
theorem dirDeriv_neg_one_le_slope {y z p q : ℝ} (hyz : y < z) (hfy : f y = (p : EReal))
    (hfz : f z = (q : EReal)) : dirDeriv f z (-1) ≤ (((p - q) / (z - y) : ℝ) : EReal) := by
  have := dirDeriv_one_le_slope (f := fun t => f (-t)) (neg_lt_neg hyz) (by simpa using hfz)
    (by simpa using hfy)
  rwa [dirDeriv_comp_neg, sub_neg_eq_add, neg_add_eq_sub] at this

/-- **The step from one point to the next**: `f'₊(y) ≤ f'₋(z)` whenever `y < z`. Together with
`f'₋ ≤ f'₊` this is the chain `f'₊(z₁) ≤ f'₋(x) ≤ f'₊(x) ≤ f'₋(z₂)` for `z₁ < x < z₂`, and it makes
both functions nondecreasing. Convexity is *not* needed: `dirDeriv` is an infimum of difference
quotients rather than a limit of them, so the two quotients across `[y, z]` bound it from above
whatever `f` is. Only `f'₋ ≤ f'₊` at a single point uses convexity. -/
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

/-- `f'₊` is nondecreasing on the whole line. -/
theorem monotone_rightDeriv (hf : ConvexFn f) (hp : ProperConvex f) : Monotone (rightDeriv f) := by
  intro y z hyz
  rcases eq_or_lt_of_le hyz with rfl | hlt
  · exact le_rfl
  exact (rightDeriv_le_leftDeriv hp hlt).trans (leftDeriv_le_rightDeriv hf hp z)

/-- `f'₋` is nondecreasing on the whole line. -/
theorem monotone_leftDeriv (hf : ConvexFn f) (hp : ProperConvex f) : Monotone (leftDeriv f) := by
  intro y z hyz
  rcases eq_or_lt_of_le hyz with rfl | hlt
  · exact le_rfl
  exact (leftDeriv_le_rightDeriv hf hp y).trans (rightDeriv_le_leftDeriv hp hlt)

end Order

/-! ### Finiteness -/

section Finite

variable {f : ℝ → EReal} {x : ℝ}

/-- `f'₊(x)` is `< +∞` exactly when some point of `dom f` lies to the right of `x` — that is,
exactly when `x` lies strictly to the left of the right endpoint of `dom f`. -/
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

/-- `f'₋(x)` is `> -∞` exactly when some point of `dom f` lies to the left of `x`. -/
theorem bot_lt_leftDeriv_iff (hp : ProperConvex f) :
    ⊥ < leftDeriv f x ↔ ∃ z, z < x ∧ f z < ⊤ := by
  rw [leftDeriv_eq_neg_rightDeriv_comp_neg, EReal.lt_neg_comm, EReal.neg_bot,
    rightDeriv_lt_top_iff (f := fun t => f (-t))
      hp.comp_neg]
  exact ⟨fun ⟨z, hz, h⟩ => ⟨-z, by linarith, h⟩,
    fun ⟨z, hz, h⟩ => ⟨-z, by linarith, by simpa using h⟩⟩

/-- **Both one-sided derivatives are finite exactly on the interior of `dom f`.** The two halves
are usually stated separately, as `f'₊ < +∞` to the left of the right endpoint and `f'₋ > -∞` to
the right of the left endpoint; on the line those two conditions together *are* interiority. -/
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

/-- Both one-sided derivatives are real at an interior point of `dom f`. -/
theorem rightDeriv_finite_of_mem_interior_convexDom (hf : ConvexFn f) (hp : ProperConvex f)
    (hx : x ∈ interior (convexDom f)) : rightDeriv f x ≠ ⊥ ∧ rightDeriv f x ≠ ⊤ := by
  obtain ⟨h1, h2⟩ := (bot_lt_leftDeriv_and_rightDeriv_lt_top_iff hf hp).2 hx
  exact ⟨(h1.trans_le (leftDeriv_le_rightDeriv hf hp x)).ne', h2.ne⟩

/-- Both one-sided derivatives are real at an interior point of `dom f`. -/
theorem leftDeriv_finite_of_mem_interior_convexDom (hf : ConvexFn f) (hp : ProperConvex f)
    (hx : x ∈ interior (convexDom f)) : leftDeriv f x ≠ ⊥ ∧ leftDeriv f x ≠ ⊤ := by
  obtain ⟨h1, h2⟩ := (bot_lt_leftDeriv_and_rightDeriv_lt_top_iff hf hp).2 hx
  exact ⟨h1.ne', ((leftDeriv_le_rightDeriv hf hp x).trans_lt h2).ne⟩

end Finite

/-! ### The subdifferential on the line -/

section Subdifferential

variable {f : ℝ → EReal} {x : ℝ}

/-- Where `f` is finite the guard in the definition of `f'₊` is inert: the difference quotients
already produce `+∞` beyond the right end of `dom f`. -/
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

/-- The mirror image: where `f` is finite, `f'₋(x) = -f'(x; -1)` with no guard. -/
theorem leftDeriv_eq_neg_dirDeriv (hx : f x < ⊤) (hb : f x ≠ ⊥) :
    leftDeriv f x = -dirDeriv f x (-1) := by
  rw [leftDeriv_eq_neg_rightDeriv_comp_neg, rightDeriv_eq_dirDeriv (by simpa using hx)
    (by simpa using hb), dirDeriv_comp_neg]

/-- **The subdifferential on the line is the interval between the one-sided derivatives**:

```
∂f(x) = {x* ∈ ℝ | f'₋(x) ≤ x* ≤ f'₊(x)}.
```

This follows from the description of `∂f x` by `f'(x; ·)`: only the directions `+1` and `-1` carry
information, because `f'(x; ·)` is positively homogeneous. -/
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

/-- A real number squeezed between the two one-sided derivatives forces `x` into `dom f`: outside
`dom f` one of the two is `±∞` on the wrong side. -/
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

/-- **The subdifferential on the line**, with no hypothesis on `x`: outside `dom f` both sides are
false. -/
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

/-! ### The limit formulas -/

section Limits

variable {f : ℝ → EReal} {x : ℝ}

/-- The estimate behind the right-hand limit formulas: if a real `μ` lies strictly below `f'₊(z)`
for every `z > x`, then `f x` is bounded by the affine function of slope `μ` through `(y, f y)`.
Along the segment from `y` down to `x`, each interior point `z` has `μ < f'₊(z) ≤` the slope from
`z` to `y`, which bounds `f z` above; closedness lets the bound pass to the endpoint `x`. -/
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

/-- **Right-continuity of `f'₊`.** For a closed proper convex function on the line the right
derivative is the limit of its own values from the right, in the monotone sense
`f'₊(x) = ⨅ {f'₊(z) | z > x}`. Closedness cannot be dropped: for `f` equal to `1` at `0`, to `0` on
`(0, ∞)` and to `⊤` on `(-∞, 0)` — convex and proper, but not closed — `f'₊` jumps at `0`. -/
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

/-- **Left-continuity of `f'₋`**: `f'₋(x) = ⨆ {f'₋(z) | z < x}` for a closed proper convex
function on the line. The reflection of `iInf_rightDeriv_Ioi`. -/
theorem iSup_leftDeriv_Iio (hf : ClosedProperConvexFn f) (x : ℝ) :
    ⨆ z ∈ Iio x, leftDeriv f z = leftDeriv f x := by
  refine le_antisymm (iSup₂_le fun z hz => monotone_leftDeriv hf.convex hf.proper hz.le) ?_
  rw [leftDeriv_eq_neg_rightDeriv_comp_neg, ← iInf_rightDeriv_Ioi hf.comp_neg (-x), EReal.neg_le]
  refine le_iInf₂ fun w hw => ?_
  rw [← neg_neg w, ← neg_neg (rightDeriv _ _), ← leftDeriv_eq_neg_rightDeriv_comp_neg]
  exact EReal.neg_le_neg_iff.2 (le_iSup₂ (f := fun z (_ : z ∈ Iio x) => leftDeriv f z) (-w)
    (show -w < x from neg_lt.2 hw))

/-- **The crossed limit formula**: the *left* derivative also has `f'₊(x)` as its limit from the
right. -/
theorem iInf_leftDeriv_Ioi (hf : ClosedProperConvexFn f) (x : ℝ) :
    ⨅ z ∈ Ioi x, leftDeriv f z = rightDeriv f x := by
  refine le_antisymm ?_ (le_iInf₂ fun z hz => rightDeriv_le_leftDeriv hf.proper hz)
  rw [← iInf_rightDeriv_Ioi hf x]
  exact iInf₂_mono fun z _ => leftDeriv_le_rightDeriv hf.convex hf.proper z

/-- **The crossed limit formula**: the *right* derivative has `f'₋(x)` as its limit from the
left. -/
theorem iSup_rightDeriv_Iio (hf : ClosedProperConvexFn f) (x : ℝ) :
    ⨆ z ∈ Iio x, rightDeriv f z = leftDeriv f x := by
  refine le_antisymm (iSup₂_le fun z hz => rightDeriv_le_leftDeriv hf.proper hz) ?_
  rw [← iSup_leftDeriv_Iio hf x]
  exact iSup₂_mono fun z _ => leftDeriv_le_rightDeriv hf.convex hf.proper z

/-! ### The four limit formulas -/

/-- `lim_{z ↓ x} f'₊(z) = f'₊(x)`. -/
theorem tendsto_rightDeriv_nhdsWithin_Ioi (hf : ClosedProperConvexFn f) (x : ℝ) :
    Tendsto (rightDeriv f) (𝓝[>] x) (𝓝 (rightDeriv f x)) := by
  simpa only [sInf_image, iInf_rightDeriv_Ioi hf x] using
    (monotone_rightDeriv hf.convex hf.proper).tendsto_nhdsGT x

/-- `lim_{z ↑ x} f'₊(z) = f'₋(x)`. -/
theorem tendsto_rightDeriv_nhdsWithin_Iio (hf : ClosedProperConvexFn f) (x : ℝ) :
    Tendsto (rightDeriv f) (𝓝[<] x) (𝓝 (leftDeriv f x)) := by
  simpa only [sSup_image, iSup_rightDeriv_Iio hf x] using
    (monotone_rightDeriv hf.convex hf.proper).tendsto_nhdsLT x

/-- `lim_{z ↓ x} f'₋(z) = f'₊(x)`. -/
theorem tendsto_leftDeriv_nhdsWithin_Ioi (hf : ClosedProperConvexFn f) (x : ℝ) :
    Tendsto (leftDeriv f) (𝓝[>] x) (𝓝 (rightDeriv f x)) := by
  simpa only [sInf_image, iInf_leftDeriv_Ioi hf x] using
    (monotone_leftDeriv hf.convex hf.proper).tendsto_nhdsGT x

/-- `lim_{z ↑ x} f'₋(z) = f'₋(x)`. -/
theorem tendsto_leftDeriv_nhdsWithin_Iio (hf : ClosedProperConvexFn f) (x : ℝ) :
    Tendsto (leftDeriv f) (𝓝[<] x) (𝓝 (leftDeriv f x)) := by
  simpa only [sSup_image, iSup_leftDeriv_Iio hf x] using
    (monotone_leftDeriv hf.convex hf.proper).tendsto_nhdsLT x

end Limits

/-! ### A nondecreasing function between the two derivatives -/

section Determination

variable {f g : ℝ → EReal}

/-- Any `φ` squeezed between the two one-sided derivatives is nondecreasing — immediately from
`f'₊(y) ≤ f'₋(z)` for `y < z`. -/
theorem monotone_of_leftDeriv_le_of_le_rightDeriv (hp : ProperConvex f) {φ : ℝ → EReal}
    (h₁ : ∀ z, leftDeriv f z ≤ φ z) (h₂ : ∀ z, φ z ≤ rightDeriv f z) : Monotone φ := by
  intro y z hyz
  rcases eq_or_lt_of_le hyz with rfl | hlt
  · exact le_rfl
  exact (h₂ y).trans ((rightDeriv_le_leftDeriv hp hlt).trans (h₁ z))

/-- **`φ` determines `f'₊`**: any nondecreasing `φ` between `f'₋` and `f'₊` has `f'₊` as its limit
from the right. -/
theorem iInf_Ioi_eq_rightDeriv (hf : ClosedProperConvexFn f) {φ : ℝ → EReal}
    (h₁ : ∀ z, leftDeriv f z ≤ φ z) (h₂ : ∀ z, φ z ≤ rightDeriv f z) (x : ℝ) :
    ⨅ z ∈ Ioi x, φ z = rightDeriv f x := by
  refine le_antisymm ?_ ?_
  · rw [← iInf_rightDeriv_Ioi hf x]
    exact iInf₂_mono fun z _ => h₂ z
  · rw [← iInf_leftDeriv_Ioi hf x]
    exact iInf₂_mono fun z _ => h₁ z

/-- **`φ` determines `f'₋`**: it has `f'₋` as its limit from the left. -/
theorem iSup_Iio_eq_leftDeriv (hf : ClosedProperConvexFn f) {φ : ℝ → EReal}
    (h₁ : ∀ z, leftDeriv f z ≤ φ z) (h₂ : ∀ z, φ z ≤ rightDeriv f z) (x : ℝ) :
    ⨆ z ∈ Iio x, φ z = leftDeriv f x := by
  refine le_antisymm ?_ ?_
  · rw [← iSup_rightDeriv_Iio hf x]
    exact iSup₂_mono fun z _ => h₂ z
  · rw [← iSup_leftDeriv_Iio hf x]
    exact iSup₂_mono fun z _ => h₁ z

/-- Two proper functions on the line with the same one-sided derivatives have the same
subdifferential — the subdifferential is the interval between them. -/
theorem subgradientRel_eq_of_deriv_eq (hpf : ProperConvex f) (hpg : ProperConvex g)
    (hr : ∀ x, rightDeriv f x = rightDeriv g x) (hl : ∀ x, leftDeriv f x = leftDeriv g x) :
    subgradientRel (innerₗ ℝ) f = subgradientRel (innerₗ ℝ) g := by
  ext p
  change p.2 ∈ subdifferential (innerₗ ℝ) f p.1 ↔ p.2 ∈ subdifferential (innerₗ ℝ) g p.1
  rw [mem_subdifferential_iff_le_rightDeriv hpf, mem_subdifferential_iff_le_rightDeriv hpg, hr, hl]

/-- **Two closed proper convex functions on the line with the same one-sided derivatives differ by
a constant.** -/
theorem exists_eq_add_coe_of_deriv_eq (hf : ClosedProperConvexFn f) (hg : ClosedProperConvexFn g)
    (hr : ∀ x, rightDeriv f x = rightDeriv g x) (hl : ∀ x, leftDeriv f x = leftDeriv g x) :
    ∃ α : ℝ, ∀ x, g x = f x + (α : EReal) := by
  have : IsCompatiblePairing ((innerₗ ℝ).flip) := by rw [flip_innerₗ]; infer_instance
  exact eq_add_coe_of_subgradientRel_subset hf hg
    (subgradientRel_eq_of_deriv_eq hf.proper hg.proper hr hl).subset

/-- **Uniqueness**: a nondecreasing `φ` between the one-sided derivatives pins down a closed
proper convex function on the line up to an additive constant. -/
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

/-- The telescoping sum around the closed cycle through a list of pairs: `chainVal` with the head
of the list as both the start and the free endpoint. The empty cycle has sum `0`. -/
def cycleVal (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : List (E × F) → ℝ
  | [] => 0
  | p :: l => chainVal B p l p.1

@[simp] theorem cycleVal_nil : cycleVal B [] = 0 := rfl

@[simp] theorem cycleVal_singleton (p : E × F) : cycleVal B [p] = 0 := by
  simp [cycleVal]

/-- Cyclic monotonicity in terms of `cycleVal`. -/
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

/-- **A cycle may be rotated by one step** without changing its sum: the last edge of the rotated
cycle is the first edge of the original. -/
theorem cycleVal_cons (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (p : E × F) (l : List (E × F)) :
    cycleVal B (p :: l) = cycleVal B (l ++ [p]) := by
  match l with
  | [] => simp
  | q :: l' =>
    change chainVal B p (q :: l') p.1 = chainVal B q (l' ++ [p]) q.1
    rw [chainVal_cons, chainVal_append_singleton]
    ring

/-- **A cycle may be rotated arbitrarily**, in the form `cycleVal (A ++ C) = cycleVal (C ++ A)`. -/
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

/-- A chain is affine in its free endpoint, with the slope realised by a pair *of the chain*. This
sharpens `exists_chainVal_eq`, and it is what makes the last edge of a cycle land on a pair to
which monotonicity applies. -/
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

/-- **Deleting the head of a cycle** changes the sum by one product. This is the induction step of
the one-dimensional theorem: if the head dominates the rest of the cycle in both coordinates, the
product is `≤ 0`. -/
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

/-- The pairing of the line with itself is multiplication. -/
theorem innerₗ_real_apply (a b : ℝ) : (innerₗ ℝ) a b = a * b := by
  simp [innerₗ_apply_apply, mul_comm]

/-- A finite nonempty list attains the maximum of a real-valued function along the list. -/
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

/-- **On the line, monotonicity is total ordering**: a mapping is monotone exactly when its graph
is a chain for the coordinatewise order on `ℝ × ℝ`, that is, a *non-decreasing curve*. -/
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

/-- **Deleting a dominating head of a cycle** does not decrease its sum. On the line this is the
whole content of the passage from monotonicity to cyclic monotonicity: the deleted edge runs
backwards in the first coordinate and forwards in the second. -/
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

/-- **On the line, monotone mappings are cyclically monotone.** A cycle may be rotated so that the
pair maximizing `x + y` comes first; monotonicity makes that pair dominate the whole cycle in both
coordinates, so deleting it does not decrease the sum, and induction on the length finishes.

In higher dimensions this fails: cyclic monotonicity is strictly stronger. -/
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

/-- **On the line the two maximality notions agree**, since the two monotonicity notions do. -/
theorem isMaximalMonotoneRel_iff_isMaximalCyclicallyMonotone :
    IsMaximalMonotoneRel (innerₗ ℝ) ρ ↔ IsMaximalCyclicallyMonotone (innerₗ ℝ) ρ := by
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁.isCyclicallyMonotone, fun σ hσ hsub => h₂ σ hσ.isMonotoneRel hsub⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁.isMonotoneRel, fun σ hσ hsub => h₂ σ hσ.isCyclicallyMonotone hsub⟩

/-- On the line the maximal monotone mappings — the maximal chains for the
coordinatewise order, the *complete non-decreasing curves* — are exactly the subdifferentials of
the closed proper convex functions. With `mem_subgradientRel_iff`, a complete non-decreasing curve
is always the region `f'₋(x) ≤ y ≤ f'₊(x)` between two one-sided derivatives, and conversely. -/
theorem isMaximalMonotoneRel_iff_exists_closedProperConvexFn :
    IsMaximalMonotoneRel (innerₗ ℝ) ρ ↔
      ∃ f : ℝ → EReal, ClosedProperConvexFn f ∧ ρ = subgradientRel (innerₗ ℝ) f := by
  have : IsCompatiblePairing ((innerₗ ℝ).flip) := by rw [flip_innerₗ]; infer_instance
  rw [isMaximalMonotoneRel_iff_isMaximalCyclicallyMonotone,
    isMaximalCyclicallyMonotone_iff_exists_closedProperConvexFn]

/-- The graph of the subdifferential of a proper convex function on the line is the region between
the two one-sided derivatives. -/
theorem mem_subgradientRel_iff (hp : ProperConvex f) {x y : ℝ} :
    ((x, y) : ℝ × ℝ) ∈ subgradientRel (innerₗ ℝ) f ↔
      leftDeriv f x ≤ (y : EReal) ∧ (y : EReal) ≤ rightDeriv f x :=
  mem_subdifferential_iff_le_rightDeriv hp

end Line

end ConvexAnalysis
