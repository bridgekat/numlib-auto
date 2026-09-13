import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Numlib.Analysis.Convex.Optimization.Perturbation
import Numlib.Analysis.Convex.Polyhedral.Duality
import Numlib.Analysis.Convex.Recession.ConeHull
import Numlib.Analysis.Convex.Subdifferential.Approx
import Numlib.Analysis.Convex.Subdifferential.Calculus
import Numlib.Analysis.Convex.Subdifferential.Existence
import NumlibSurface.Rockafellar.Part3.Section16
import NumlibSurface.Rockafellar.Part4.Section19

/-!
# Rockafellar, §23: Directional Derivatives and Subgradients

The one-sided directional derivative `f'(x; y)`, the subdifferential `∂f(x)`, and the duality
`x* ∈ ∂f(x) ⟺ f(x) + f*(x*) = ⟨x, x*⟩` that makes the two calculable. This is where Parts II and
III are cashed in: Theorem 23.2 is Corollary 13.2.1 applied to `f'(x; ·)`, Theorem 23.4 is Theorem
7.2 with Corollary 7.4.2, Theorem 23.8 is Theorem 16.4, and Theorem 23.9 is Theorem 16.3.

All sixteen numbered results of §23 are formalized over `Rn n = ℝⁿ`: Theorems 23.1–23.10 and
Corollaries 23.5.1–23.5.4, 23.7.1, 23.8.1.

Both of the section's objects are backbone definitions. `dirDeriv f x y` is `f'(x; y)`, *defined*
as the infimum of the difference quotient over `λ > 0`; the book defines it as the limit as `λ ↓ 0`
and proves in Theorem 23.1 that the two agree, which here is `theorem_23_1_monotone`.
`subdifferential (pairing n) f x` is `∂f(x)`, and `subgradientRel (pairing n) f` is the multivalued
mapping `∂f` as a `SetRel`, so that Corollary 23.5.1 is `SetRel.inv` applied to it. `normalCone` is
`N_C(x)` and `epsSubdifferential` is `∂_ε f(x)`.

## References

* [rockafellar1970convex] §23.
-/

open Set Pointwise

namespace Rockafellar

open ConvexAnalysis NumlibSurface

variable {m n : ℕ}

/-! ### Theorem 23.1: the one-sided directional derivative -/

/-- **Theorem 23.1**, first assertion. For convex `f` finite at `x`, the difference quotient
`[f(x + λy) - f(x)] / λ` is non-decreasing in `λ > 0`. This is what identifies the book's
`lim_{λ ↓ 0}` with the infimum that defines `dirDeriv`. -/
theorem theorem_23_1_monotone {f : Rn n → EReal} (hf : ConvexFn f) {x : Rn n} {r : ℝ}
    (hr : f x = (r : EReal)) (y : Rn n) :
    MonotoneOn (fun a : ℝ => (f (x + a • y) - f x) / (a : EReal)) (Ioi 0) :=
  monotoneOn_sub_div hf hr y

/-- **Theorem 23.1**, the formula `f'(x; y) = inf_{λ > 0} [f(x + λy) - f(x)] / λ`, which here is
the definition of `dirDeriv`. -/
theorem theorem_23_1_iInf (f : Rn n → EReal) (x y : Rn n) :
    dirDeriv f x y = ⨅ a ∈ Ioi (0 : ℝ), (f (x + a • y) - f x) / (a : EReal) :=
  dirDeriv_apply f x y

/-- **Theorem 23.1**: `f'(x; ·)` is positively homogeneous. This clause needs neither convexity of
`f` nor finiteness at `x`, being a reindexing of the infimum. -/
theorem theorem_23_1_posHomogeneous (f : Rn n → EReal) (x : Rn n) :
    PosHomogeneous (dirDeriv f x) :=
  posHomogeneous_dirDeriv f x

/-- **Theorem 23.1**: `f'(x; ·)` is a convex function of `y`. Finiteness of `f` at `x` is not
removable: off `dom f` the difference quotient is `⊤ - ⊤ = ⊥` in every direction. -/
theorem theorem_23_1_convex {f : Rn n → EReal} (hf : ConvexFn f) {x : Rn n} (ht : f x ≠ ⊤)
    (hb : f x ≠ ⊥) : ConvexFn (dirDeriv f x) :=
  convexFn_dirDeriv hf ht hb

/-- **Theorem 23.1**: `f'(x; 0) = 0`. -/
theorem theorem_23_1_zero {f : Rn n → EReal} {x : Rn n} (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) :
    dirDeriv f x 0 = 0 :=
  dirDeriv_zero ht hb

/-- **Theorem 23.1**, last assertion: `-f'(x; -y) ≤ f'(x; y)` for every `y`. -/
theorem theorem_23_1_neg_le {f : Rn n → EReal} (hf : ConvexFn f) {x : Rn n} (ht : f x ≠ ⊤)
    (hb : f x ≠ ⊥) (y : Rn n) : -dirDeriv f x (-y) ≤ dirDeriv f x y :=
  neg_dirDeriv_neg_le hf ht hb y

/-! ### Theorem 23.2: subgradients and directional derivatives -/

/-- **Theorem 23.2**. For convex `f` finite at `x`, `x* ∈ ∂f(x)` iff `f'(x; y) ≥ ⟨x*, y⟩` for
every `y`. Convexity is not used: the subgradient inequality and the infimum of difference
quotients are two spellings of the same system. -/
theorem theorem_23_2 {f : Rn n → EReal} {x : Rn n} (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) {y : Rn n} :
    y ∈ subdifferential (pairing n) f x ↔
      ∀ v : Rn n, ((pairing n v y : ℝ) : EReal) ≤ dirDeriv f x v :=
  mem_subdifferential_iff_le_dirDeriv ht hb

/-- **Theorem 23.2**, second assertion: the closure of `f'(x; ·)` as a convex function of `y` is
the support function of the closed convex set `∂f(x)`. -/
theorem theorem_23_2_closure {f : Rn n → EReal} (hf : ConvexFn f) {x : Rn n} (ht : f x ≠ ⊤)
    (hb : f x ≠ ⊥) :
    clFn (dirDeriv f x) = supportFn (pairing n) (subdifferential (pairing n) f x) := by
  have h := clFn_dirDeriv (B := pairing n) hf ht hb
  rwa [flip_pairing] at h

/-! ### Theorem 23.3: when subgradients exist -/

/-- **Theorem 23.3**, first assertion: a function subdifferentiable at a point where it is finite
is proper — a subgradient exhibits an affine minorant. -/
theorem theorem_23_3_proper {f : Rn n → EReal} {x : Rn n} (ht : f x ≠ ⊤) (hb : f x ≠ ⊥)
    (h : (subdifferential (pairing n) f x).Nonempty) : Proper f :=
  proper_of_subdifferential_nonempty ht hb h

/-- **Theorem 23.3**, second assertion: if `f` is *not* subdifferentiable at `x`, some direction
has `f'(x; y) = -f'(x; -y) = -∞`. The book's `-f'(x; -y) = -∞` is stated here as
`f'(x; -y) = +∞`. -/
theorem theorem_23_3_two_sided {f : Rn n → EReal} (hf : ConvexFn f) {x : Rn n} (ht : f x ≠ ⊤)
    (hb : f x ≠ ⊥) (hsub : subdifferential (pairing n) f x = ∅) :
    ∃ y : Rn n, dirDeriv f x y = ⊥ ∧ dirDeriv f x (-y) = ⊤ :=
  exists_dirDeriv_eq_bot_and_dirDeriv_neg_eq_top hf ht hb hsub

/-- **Theorem 23.3**, last assertion: if `f` is not subdifferentiable at `x` then
`f'(x; z - x) = -∞` for *every* `z ∈ ri (dom f)`. -/
theorem theorem_23_3_relint {f : Rn n → EReal} (hf : ConvexFn f) {x : Rn n} (ht : f x ≠ ⊤)
    (hb : f x ≠ ⊥) (hsub : subdifferential (pairing n) f x = ∅) {z : Rn n} (hz : z ∈ ri (dom f)) :
    dirDeriv f x (z - x) = ⊥ :=
  dirDeriv_eq_bot_of_subdifferential_eq_empty hf ht hb hsub hz

/-! ### Theorem 23.4: existence, closedness and boundedness -/

/-- **Theorem 23.4**, first assertion: `∂f(x) = ∅` for `x ∉ dom f`. Convexity is not used. -/
theorem theorem_23_4_notMem_dom {f : Rn n → EReal} (hp : Proper f) {x : Rn n} (hx : x ∉ dom f) :
    subdifferential (pairing n) f x = ∅ :=
  subdifferential_eq_empty_of_notMem_dom hp hx

/-- **Theorem 23.4**: a proper convex function is subdifferentiable at every point of
`ri (dom f)`. -/
theorem theorem_23_4_nonempty {f : Rn n → EReal} (hf : ConvexFn f) (hp : Proper f) {x : Rn n}
    (hx : x ∈ ri (dom f)) : (subdifferential (pairing n) f x).Nonempty :=
  subdifferential_nonempty_of_mem_relint_dom hf hp hx

/-- **Theorem 23.4**: for `x ∈ ri (dom f)`, `f'(x; ·)` is proper. -/
theorem theorem_23_4_proper {f : Rn n → EReal} (hf : ConvexFn f) (hp : Proper f) {x : Rn n}
    (hx : x ∈ ri (dom f)) : Proper (dirDeriv f x) :=
  proper_dirDeriv_of_mem_relint_dom hf hp hx

/-- **Theorem 23.4**: for `x ∈ ri (dom f)`, `f'(x; ·)` is closed. -/
theorem theorem_23_4_closed {f : Rn n → EReal} (hf : ConvexFn f) (hp : Proper f) {x : Rn n}
    (hx : x ∈ ri (dom f)) : ClosedFn (dirDeriv f x) :=
  closedFn_dirDeriv_of_mem_relint_dom hf hp hx

/-- **Theorem 23.4**: for `x ∈ ri (dom f)`, `f'(x; y) = δ*(y | ∂f(x))`. Because `f'(x; ·)` is
already closed there no closure appears — this is the sharpening of Theorem 23.2 that the relative
interior buys. -/
theorem theorem_23_4_supportFn {f : Rn n → EReal} (hf : ConvexFn f) (hp : Proper f) {x : Rn n}
    (hx : x ∈ ri (dom f)) :
    dirDeriv f x = supportFn (pairing n) (subdifferential (pairing n) f x) := by
  have h := dirDeriv_eq_supportFn_of_mem_relint_dom (B := pairing n) hf hp hx
  rwa [flip_pairing] at h

/-- **Theorem 23.4**, last assertion: `∂f(x)` is non-empty and *bounded* iff
`x ∈ int (dom f)`. -/
theorem theorem_23_4_isBounded_iff {f : Rn n → EReal} (hf : ConvexFn f) (hp : Proper f)
    {x : Rn n} (hx : x ∈ ri (dom f)) :
    Bornology.IsBounded (subdifferential (pairing n) f x) ↔ x ∈ interior (dom f) :=
  isBounded_subdifferential_iff_mem_interior_dom hf hp hx

/-- **Theorem 23.4**, last clause: in that case `f'(x; y)` is finite for every `y`. "Finite" is
`dom (f'(x; ·)) = ℝⁿ` together with properness, which rules out `-∞`. -/
theorem theorem_23_4_finite_iff {f : Rn n → EReal} (hf : ConvexFn f) (hp : Proper f) {x : Rn n}
    (hx : x ∈ ri (dom f)) : dom (dirDeriv f x) = univ ↔ x ∈ interior (dom f) :=
  dom_dirDeriv_eq_univ_iff_mem_interior_dom hf hp hx

/-! ### `dom ∂f` need not be convex

Theorem 23.4 places the set of points at which a proper convex function is subdifferentiable
between `ri (dom f)` and `dom f`. Rockafellar observes (p. 218) that it need not be convex, and
gives the example transcribed here. -/

/-- **p. 218.** The function `f(ξ₁, ξ₂) = max {g(ξ₁), |ξ₂|}` on `ℝ²`, where `g(ξ₁) = 1 - ξ₁^{1/2}`
for `ξ₁ ≥ 0` and `+∞` for `ξ₁ < 0`. Its effective domain is the closed right half-plane, and it is
subdifferentiable everywhere on that half-plane **except** in the relative interior of the segment
joining `(0, 1)` and `(0, -1)`, so `dom ∂f` is not convex. -/
noncomputable def nonsmoothMaxFn : Rn 2 → EReal :=
  ConvexAnalysis.restrictFn {x : Rn 2 | 0 ≤ x 0}
    fun x => ((max (1 - Real.sqrt (x 0)) |x 1| : ℝ) : EReal)

private theorem convexOn_nonsmoothMax :
    ConvexOn ℝ {x : Rn 2 | 0 ≤ x 0} fun x => max (1 - Real.sqrt (x 0)) |x 1| := by
  have hconv : Convex ℝ {x : Rn 2 | 0 ≤ x 0} := by
    intro u hu v hv a b ha hb _
    have hu' : (0 : ℝ) ≤ u 0 := hu
    have hv' : (0 : ℝ) ≤ v 0 := hv
    have hcoord : (a • u + b • v) 0 = a * u 0 + b * v 0 := by simp
    change (0 : ℝ) ≤ (a • u + b • v) 0
    rw [hcoord]
    positivity
  refine ⟨hconv, fun u hu v hv a b ha hb hab => ?_⟩
  have hu' : (0 : ℝ) ≤ u 0 := hu
  have hv' : (0 : ℝ) ≤ v 0 := hv
  have hc0 : (a • u + b • v) 0 = a * u 0 + b * v 0 := by simp
  have hc1 : (a • u + b • v) 1 = a * u 1 + b * v 1 := by simp
  have hsqrt : a * Real.sqrt (u 0) + b * Real.sqrt (v 0)
      ≤ Real.sqrt (a * u 0 + b * v 0) := by
    have h := Real.strictConcaveOn_sqrt.concaveOn.2 (Set.mem_Ici.2 hu') (Set.mem_Ici.2 hv') ha hb
      hab
    simpa using h
  have habs : |a * u 1 + b * v 1| ≤ a * |u 1| + b * |v 1| := by
    calc |a * u 1 + b * v 1| ≤ |a * u 1| + |b * v 1| := abs_add_le _ _
      _ = a * |u 1| + b * |v 1| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  simp only [hc0, hc1, smul_eq_mul]
  refine max_le ?_ ?_
  · have hexp : a * (1 - Real.sqrt (u 0)) + b * (1 - Real.sqrt (v 0))
        = 1 - (a * Real.sqrt (u 0) + b * Real.sqrt (v 0)) := by linear_combination hab
    have hstep : 1 - Real.sqrt (a * u 0 + b * v 0)
        ≤ a * (1 - Real.sqrt (u 0)) + b * (1 - Real.sqrt (v 0)) := by
      rw [hexp]; linarith
    exact hstep.trans (add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
      (mul_le_mul_of_nonneg_left (le_max_left _ _) hb))
  · exact habs.trans (add_le_add (mul_le_mul_of_nonneg_left (le_max_right _ _) ha)
      (mul_le_mul_of_nonneg_left (le_max_right _ _) hb))

private theorem convexFn_nonsmoothMaxFn : ConvexFn nonsmoothMaxFn :=
  (convexOn_iff_convexFn _ _).1 convexOn_nonsmoothMax

private theorem nonsmoothMaxFn_of_nonneg {x : Rn 2} (hx : 0 ≤ x 0) :
    nonsmoothMaxFn x = ((max (1 - Real.sqrt (x 0)) |x 1| : ℝ) : EReal) :=
  ConvexAnalysis.restrictFn_of_mem hx

private theorem nonsmoothMaxFn_of_neg {x : Rn 2} (hx : ¬ 0 ≤ x 0) : nonsmoothMaxFn x = ⊤ :=
  ConvexAnalysis.restrictFn_of_notMem hx

private noncomputable def upperPoint : Rn 2 := WithLp.toLp 2 ![(0 : ℝ), 1]

private noncomputable def lowerPoint : Rn 2 := WithLp.toLp 2 ![(0 : ℝ), -1]

private theorem mem_subdifferential_upperPoint :
    upperPoint ∈ subdifferential (pairing 2) nonsmoothMaxFn upperPoint := by
  have h0 : upperPoint 0 = (0 : ℝ) := rfl
  have h1 : upperPoint 1 = (1 : ℝ) := rfl
  have hval : nonsmoothMaxFn upperPoint = ((1 : ℝ) : EReal) := by
    rw [nonsmoothMaxFn_of_nonneg (by rw [h0]), h0, h1]
    norm_num
  intro z
  rw [hval, pairing_two]
  simp only [PiLp.sub_apply, h0, h1]
  by_cases hz : 0 ≤ z 0
  · rw [nonsmoothMaxFn_of_nonneg hz]
    have : (1 : ℝ) + ((z 0 - 0) * 0 + (z 1 - 1) * 1) ≤ max (1 - Real.sqrt (z 0)) |z 1| := by
      have := le_max_right (1 - Real.sqrt (z 0)) |z 1|
      have hle : z 1 ≤ |z 1| := le_abs_self _
      linarith
    exact_mod_cast this
  · rw [nonsmoothMaxFn_of_neg hz]
    exact le_top

private theorem mem_subdifferential_lowerPoint :
    lowerPoint ∈ subdifferential (pairing 2) nonsmoothMaxFn lowerPoint := by
  have h0 : lowerPoint 0 = (0 : ℝ) := rfl
  have h1 : lowerPoint 1 = (-1 : ℝ) := rfl
  have hval : nonsmoothMaxFn lowerPoint = ((1 : ℝ) : EReal) := by
    rw [nonsmoothMaxFn_of_nonneg (by rw [h0]), h0, h1]
    norm_num
  intro z
  rw [hval, pairing_two]
  simp only [PiLp.sub_apply, h0, h1]
  by_cases hz : 0 ≤ z 0
  · rw [nonsmoothMaxFn_of_nonneg hz]
    have : (1 : ℝ) + ((z 0 - 0) * 0 + (z 1 - -1) * -1) ≤ max (1 - Real.sqrt (z 0)) |z 1| := by
      have := le_max_right (1 - Real.sqrt (z 0)) |z 1|
      have hle : -z 1 ≤ |z 1| := neg_le_abs _
      linarith
    exact_mod_cast this
  · rw [nonsmoothMaxFn_of_neg hz]
    exact le_top

/-- `f` is finite at the origin, but the difference quotient in the direction `(1, 0)` behaves like
`-λ^{-1/2}`, so `f'(0; (1,0)) = -∞` and `∂f(0) = ∅`. -/
private theorem subdifferential_nonsmoothMaxFn_zero :
    subdifferential (pairing 2) nonsmoothMaxFn 0 = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro y hy
  have hz0 : (0 : Rn 2) 0 = (0 : ℝ) := rfl
  have hz1 : (0 : Rn 2) 1 = (0 : ℝ) := rfl
  have hval : nonsmoothMaxFn 0 = ((1 : ℝ) : EReal) := by
    rw [nonsmoothMaxFn_of_nonneg (by rw [hz0]), hz0, hz1]
    norm_num
  set t : ℝ := 1 / (|y 0| + 1) with htdef
  have habs : (0 : ℝ) ≤ |y 0| := abs_nonneg _
  have hpos : (0 : ℝ) < |y 0| + 1 := by linarith
  have ht0 : 0 < t := by rw [htdef]; positivity
  have ht1 : t ≤ 1 := by
    rw [htdef, div_le_one hpos]
    linarith
  set z : Rn 2 := WithLp.toLp 2 ![t ^ 2, (0 : ℝ)] with hzdef
  have hz0' : z 0 = t ^ 2 := rfl
  have hz1' : z 1 = (0 : ℝ) := rfl
  have hsq : Real.sqrt (z 0) = t := by rw [hz0', Real.sqrt_sq ht0.le]
  have hzval : nonsmoothMaxFn z = ((1 - t : ℝ) : EReal) := by
    rw [nonsmoothMaxFn_of_nonneg (by rw [hz0']; positivity), hsq, hz1']
    have : max (1 - t) |(0 : ℝ)| = 1 - t := by
      rw [abs_zero]
      exact max_eq_left (by linarith)
    rw [this]
  have hsub := hy z
  rw [hval, hzval, pairing_two] at hsub
  simp only [PiLp.sub_apply, hz0, hz1, hz0', hz1'] at hsub
  have hreal : (1 : ℝ) + ((t ^ 2 - 0) * y 0 + (0 - 0) * y 1) ≤ 1 - t := by exact_mod_cast hsub
  have hkey : t * y 0 ≤ -1 := by
    have h2 : t ^ 2 * y 0 ≤ -t := by nlinarith
    nlinarith [ht0]
  have hbound : -1 < t * y 0 := by
    have h1 : -(t * |y 0|) ≤ t * y 0 := by
      have := neg_abs_le (y 0)
      nlinarith [ht0.le]
    have h2 : t * |y 0| < 1 := by
      rw [htdef, div_mul_eq_mul_div, one_mul, div_lt_one hpos]
      linarith
    linarith
  linarith

/-- **p. 218**: the set of points at which a proper convex function is subdifferentiable need not
be convex. `dom ∂f` contains `(0, 1)` and `(0, -1)` but not their midpoint `(0, 0)`; this is why
Theorem 23.4 can only *sandwich* `dom ∂f` between `ri (dom f)` and `dom f`. -/
theorem notConvex_domSubdifferential_nonsmoothMaxFn :
    ¬ Convex ℝ (domSubdifferential (pairing 2) nonsmoothMaxFn) := by
  intro hconv
  have hup : upperPoint ∈ domSubdifferential (pairing 2) nonsmoothMaxFn :=
    ⟨upperPoint, mem_subdifferential_upperPoint⟩
  have hlow : lowerPoint ∈ domSubdifferential (pairing 2) nonsmoothMaxFn :=
    ⟨lowerPoint, mem_subdifferential_lowerPoint⟩
  have hmid := hconv hup hlow (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num)
  have hzero : (1/2 : ℝ) • upperPoint + (1/2 : ℝ) • lowerPoint = (0 : Rn 2) := by
    ext j
    fin_cases j <;> simp [upperPoint, lowerPoint]
  rw [hzero] at hmid
  obtain ⟨y, hy⟩ := hmid
  rw [subdifferential_nonsmoothMaxFn_zero] at hy
  exact hy

/-- The example really is a *proper convex* function, so it witnesses the statement the book
makes. -/
theorem proper_convexFn_nonsmoothMaxFn : ConvexFn nonsmoothMaxFn ∧ Proper nonsmoothMaxFn := by
  refine ⟨convexFn_nonsmoothMaxFn, ⟨⟨0, ?_⟩, fun x => ?_⟩⟩
  · have hz0 : (0 : Rn 2) 0 = (0 : ℝ) := rfl
    rw [mem_dom, nonsmoothMaxFn_of_nonneg (by rw [hz0])]
    exact EReal.coe_lt_top _
  · by_cases hx : 0 ≤ x 0
    · rw [nonsmoothMaxFn_of_nonneg hx]
      exact EReal.coe_ne_bot _
    · rw [nonsmoothMaxFn_of_neg hx]
      exact top_ne_bot

/-! ### Theorem 23.5: the four conditions, and the three starred ones -/

/-- **Theorem 23.5**, condition (a): `x* ∈ ∂f(x)`, that is `f(z) ≥ f(x) + ⟨x*, z - x⟩` for every
`z`. Recorded as a clause so that the seven conditions read off one list. -/
theorem theorem_23_5_a {f : Rn n → EReal} {x y : Rn n} :
    y ∈ subdifferential (pairing n) f x ↔
      ∀ z : Rn n, f x + ((pairing n (z - x) y : ℝ) : EReal) ≤ f z :=
  mem_subdifferential

/-- **Theorem 23.5**, condition (b): `⟨z, x*⟩ - f(z)` attains its supremum in `z` at `z = x`.
Neither convexity nor properness is used, this being the subgradient inequality with the terms
moved across. -/
theorem theorem_23_5_b {f : Rn n → EReal} {x y : Rn n} :
    y ∈ subdifferential (pairing n) f x ↔
      ∀ z : Rn n, ((pairing n z y : ℝ) : EReal) - f z ≤ ((pairing n x y : ℝ) : EReal) - f x :=
  mem_subdifferential_iff_forall_sub_le

/-- **Theorem 23.5**, condition (c): `f(x) + f*(x*) ≤ ⟨x, x*⟩`. Since the supremum in (b) *is*
`f*(x*)`, this is (b) restated; again no hypothesis is needed. -/
theorem theorem_23_5_c {f : Rn n → EReal} {x y : Rn n} :
    y ∈ subdifferential (pairing n) f x ↔
      f x + conj (pairing n) f y ≤ ((pairing n x y : ℝ) : EReal) :=
  mem_subdifferential_iff_add_conj_le

/-- **Theorem 23.5**, condition (d): `f(x) + f*(x*) = ⟨x, x*⟩`. This is the one clause of (a)–(d)
that genuinely consumes properness: Fenchel's inequality `⟨x, x*⟩ ≤ f(x) + f*(x*)` is false for
`f ≡ +∞`, since `⊤ + ⊥ = ⊥` in `EReal`. -/
theorem theorem_23_5_d {f : Rn n → EReal} (hp : Proper f) {x y : Rn n} :
    y ∈ subdifferential (pairing n) f x ↔
      f x + conj (pairing n) f y = ((pairing n x y : ℝ) : EReal) :=
  hp.mem_subdifferential_iff_add_conj_eq

/-- **Theorem 23.5**, condition (a*): `x ∈ ∂f*(x*)`, available when `(cl f)(x) = f(x)` — which for
convex `f` is Fenchel–Moreau's `f** x = f x`. -/
theorem theorem_23_5_a_star {f : Rn n → EReal} (hf : ConvexFn f) {x : Rn n}
    (hx : clFn f x = f x) {y : Rn n} :
    x ∈ subdifferential (pairing n) (conj (pairing n) f) y ↔
      y ∈ subdifferential (pairing n) f x := by
  have hbi : biconj (pairing n) f x = f x := by rw [biconj_eq_clFn hf]; exact hx
  have h := mem_subdifferential_conj_iff (B := pairing n) (f := f) (x := x) (y := y) hbi
  rwa [flip_pairing] at h

/-- **Theorem 23.5**, condition (b*): `⟨x, z*⟩ - f*(z*)` attains its supremum in `z*` at `z* = x*`,
available when `(cl f)(x) = f(x)`. -/
theorem theorem_23_5_b_star {f : Rn n → EReal} (hf : ConvexFn f) {x : Rn n}
    (hx : clFn f x = f x) {y : Rn n} :
    y ∈ subdifferential (pairing n) f x ↔
      ∀ w : Rn n, ((pairing n x w : ℝ) : EReal) - conj (pairing n) f w
        ≤ ((pairing n x y : ℝ) : EReal) - conj (pairing n) f y := by
  rw [← theorem_23_5_a_star hf hx, theorem_23_5_b]
  exact forall_congr' fun w => by rw [pairing_comm w x, pairing_comm y x]

/-- **Theorem 23.5**, condition (a**): `x* ∈ ∂(cl f)(x)`, available when `(cl f)(x) = f(x)`. -/
theorem theorem_23_5_a_star_star {f : Rn n → EReal} {x : Rn n} (hx : clFn f x = f x)
    {y : Rn n} :
    y ∈ subdifferential (pairing n) (clFn f) x ↔ y ∈ subdifferential (pairing n) f x :=
  mem_subdifferential_clFn_iff hx

/-- **Corollary 23.5.1**. For a closed proper convex `f`, the multivalued mapping `∂f*` is the
inverse of `∂f` — literally `SetRel.inv` applied to `subgradientRel`. **The book states this
corollary with no proof**; it follows from the equivalence of (a) and (a*) in Theorem 23.5, whose
hypothesis `(cl f)(x) = f(x)` is automatic for a closed `f`. -/
theorem corollary_23_5_1 {f : Rn n → EReal} (hf : ConvexFn f) (hc : ClosedFn f) :
    subgradientRel (pairing n) (conj (pairing n) f) = (subgradientRel (pairing n) f).inv := by
  have h := subgradientRel_conj_eq_inv (B := pairing n) hf hc
  rwa [flip_pairing] at h

/-- **Corollary 23.5.1**, pointwise: `x ∈ ∂f*(x*)` iff `x* ∈ ∂f(x)`. -/
theorem corollary_23_5_1_mem {f : Rn n → EReal} (hf : ConvexFn f) (hc : ClosedFn f)
    {x y : Rn n} :
    x ∈ subdifferential (pairing n) (conj (pairing n) f) y ↔
      y ∈ subdifferential (pairing n) f x := by
  have h := mem_subdifferential_conj_iff_of_closedFn (B := pairing n) (x := x) (y := y) hf hc
  rwa [flip_pairing] at h

/-- **Corollary 23.5.2**, first assertion: if `f` is subdifferentiable at `x` then
`(cl f)(x) = f(x)`. Properness is not needed. -/
theorem corollary_23_5_2_clFn {f : Rn n → EReal} (hf : ConvexFn f) {x y : Rn n}
    (hy : y ∈ subdifferential (pairing n) f x) : clFn f x = f x :=
  clFn_eq_of_mem_subdifferential hf hy

/-- **Corollary 23.5.2**, second assertion: and then `∂(cl f)(x) = ∂f(x)`. -/
theorem corollary_23_5_2_subdifferential {f : Rn n → EReal} (hf : ConvexFn f) {x y : Rn n}
    (hy : y ∈ subdifferential (pairing n) f x) :
    subdifferential (pairing n) (clFn f) x = subdifferential (pairing n) f x :=
  subdifferential_clFn hf hy

/-- **Corollary 23.5.3**. For a non-empty closed convex `C`, `∂δ*(x* | C)` consists of the points
of `C` (if any) at which `⟨·, x*⟩ ` attains its maximum over `C`. -/
theorem corollary_23_5_3 {C : Set (Rn n)} (hC : IsClosed C) (hCc : Convex ℝ C)
    (hCne : C.Nonempty) (y : Rn n) :
    subdifferential (pairing n) (supportFn (pairing n) C) y
      = {x ∈ C | ∀ z ∈ C, pairing n z y ≤ pairing n x y} := by
  have h := subdifferential_supportFn (B := pairing n) hC hCc hCne y
  rwa [flip_pairing] at h

private theorem normalCone_zero (C : Set (Rn n)) :
    normalCone (pairing n) C 0 = polarCone (pairing n) C := by
  ext y
  simp only [mem_normalCone, mem_polarCone, sub_zero]

/-- **Corollary 23.5.4**. For a convex cone `K`, `x* ∈ ∂δ(x | K)` iff `x ∈ K`, `x* ∈ K°` and
`⟨x, x*⟩ = 0` — the complementary-slackness form. **Rockafellar assumes `K` non-empty and closed
and neither hypothesis is used**: he derives the corollary from `δ(· | K)* = δ(· | K°)`, which needs
closedness, whereas putting `z = 0` and `z = x + x` into the subgradient inequality does not. -/
theorem corollary_23_5_4 (K : PointedCone ℝ (Rn n)) {x y : Rn n} :
    y ∈ subdifferential (pairing n) (indicatorFn (K : Set (Rn n))) x ↔
      x ∈ K ∧ y ∈ polarCone (pairing n) (K : Set (Rn n)) ∧ pairing n x y = 0 := by
  rw [mem_subdifferential_indicatorFn_pointedCone, normalCone_zero]

/-- **Corollary 23.5.4**, the duality: for a *closed* convex cone `K`, `x* ∈ ∂δ(x | K)` iff
`x ∈ ∂δ(x* | K°)`. Both sides unfold to the same three conditions once `K°° = K` (Theorem 14.1)
identifies the polar of `K°` with `K`. Closedness is used here and only here. -/
theorem corollary_23_5_4_inv {K : PointedCone ℝ (Rn n)} (hK : IsClosed (K : Set (Rn n)))
    {x y : Rn n} :
    y ∈ subdifferential (pairing n) (indicatorFn (K : Set (Rn n))) x ↔
      x ∈ subdifferential (pairing n)
        (indicatorFn (polarPointedCone (pairing n) (K : Set (Rn n)) : Set (Rn n))) y := by
  have hbi : polarCone (pairing n) (polarCone (pairing n) (K : Set (Rn n)))
      = (K : Set (Rn n)) := by
    have h := polarCone_polarCone_pointedCone (B := pairing n) K hK
    rwa [flip_pairing] at h
  rw [corollary_23_5_4, corollary_23_5_4 (polarPointedCone (pairing n) (K : Set (Rn n)))]
  rw [coe_polarPointedCone, hbi]
  constructor
  · rintro ⟨hx, hy, h0⟩
    exact ⟨hy, hx, by rw [NumlibSurface.pairing_comm]; exact h0⟩
  · rintro ⟨hy, hx, h0⟩
    exact ⟨hx, hy, by rw [NumlibSurface.pairing_comm]; exact h0⟩

/-! ### Theorem 23.6: `ε`-subgradients -/

/-- An unnumbered fact recorded before Theorem 23.6: `∂_ε f(x)` is a closed convex set for every
`ε`, being `{x* | h*(x*) ≤ ε}` for `h(y) = f(x + y) - f(x)`. -/
theorem epsSubdifferential_convex_closed {f : Rn n → EReal} {x : Rn n} {r : ℝ}
    (hr : f x = (r : EReal)) (ε : ℝ) :
    Convex ℝ (epsSubdifferential (pairing n) ε f x) ∧
      IsClosed (epsSubdifferential (pairing n) ε f x) :=
  ⟨convex_epsSubdifferential hr ε, isClosed_epsSubdifferential hr ε⟩

/-- The other unnumbered fact: the nest `∂_ε f(x)`, `ε > 0`, has intersection `∂f(x)`. -/
theorem epsSubdifferential_iInter (f : Rn n → EReal) (x : Rn n) :
    ⋂ ε ∈ Ioi (0 : ℝ), epsSubdifferential (pairing n) ε f x = subdifferential (pairing n) f x :=
  iInter_epsSubdifferential (pairing n) f x

/-- **Theorem 23.6**. For a closed proper convex `f` finite at `x`,
`f'(x; y) = lim_{ε ↓ 0} δ*(y | ∂_ε f(x))`. The sets `∂_ε f(x)` increase with `ε`, so the book's
limit is written here as the infimum it is; and "closed" is spelled as `IsClosed (epi f)`, which
for a proper convex function is the same condition. -/
theorem theorem_23_6 {f : Rn n → EReal} (hf : ConvexFn f) (hp : Proper f)
    (hc : IsClosed (epi f)) {x : Rn n} {r : ℝ} (hr : f x = (r : EReal)) (v : Rn n) :
    ⨅ ε ∈ Ioi (0 : ℝ), supportFn (pairing n) (epsSubdifferential (pairing n) ε f x) v
      = dirDeriv f x v := by
  have h := dirDeriv_eq_iInf_supportFn_epsSubdifferential (B := pairing n) hf hp hc hr v
  simpa only [flip_pairing] using h

/-! ### Theorem 23.7: normals to a level set -/

/-- **Theorem 23.7**. If `f` is proper convex and subdifferentiable at `x` but does not attain its
minimum there, the normal cone at `x` to `C = {z | f(z) ≤ f(x)}` is the closure of the convex cone
generated by `∂f(x)`. The hypothesis `⨅ z, f z < f x` is "does not attain its minimum". -/
theorem theorem_23_7 {f : Rn n → EReal} (hf : ConvexFn f) {x : Rn n} {r : ℝ}
    (hr : f x = (r : EReal)) (hinf : ⨅ z, f z < (r : EReal))
    (hne : (subdifferential (pairing n) f x).Nonempty) :
    normalCone (pairing n) {z | f z ≤ (r : EReal)} x
      = closure ((PointedCone.hull ℝ (subdifferential (pairing n) f x) : Set (Rn n))) :=
  normalCone_setOf_le_eq_closure_coe_hull_subdifferential hf hr hinf hne

/-- **Corollary 23.7.1**. If `x ∈ int (dom f)` and `f` does not attain its minimum there, the
closure in Theorem 23.7 is unnecessary: the normal cone is the convex cone generated by `∂f(x)`.
What makes the closure redundant is that `∂f(x)` is then non-empty, closed, bounded and misses the
origin, so Corollary 9.6.1 applies. -/
theorem corollary_23_7_1 {f : Rn n → EReal} (hf : ConvexFn f) (hp : Proper f) {x : Rn n} {r : ℝ}
    (hr : f x = (r : EReal)) (hinf : ⨅ z, f z < (r : EReal)) (hx : x ∈ interior (dom f)) :
    normalCone (pairing n) {z | f z ≤ (r : EReal)} x
      = (PointedCone.hull ℝ (subdifferential (pairing n) f x) : Set (Rn n)) :=
  normalCone_setOf_le_eq_coe_hull_subdifferential_of_mem_interior_dom hf hp hr hinf hx

/-- **Corollary 23.7.1** in the book's own words: `x*` is normal to `C = {z | f(z) ≤ f(x)}` at `x`
iff `x* ∈ λ ∂f(x)` for some `λ ≥ 0`. The convex cone generated by a *convex* set is the union of
its non-negative multiples (Corollary 9.6.1), and `∂f(x)` is non-empty here, which is what turns
`λ > 0` into `λ ≥ 0`. -/
theorem corollary_23_7_1_smul {f : Rn n → EReal} (hf : ConvexFn f) (hp : Proper f) {x : Rn n}
    {r : ℝ} (hr : f x = (r : EReal)) (hinf : ⨅ z, f z < (r : EReal))
    (hx : x ∈ interior (dom f)) {y : Rn n} :
    y ∈ normalCone (pairing n) {z | f z ≤ (r : EReal)} x ↔
      ∃ a : ℝ, 0 ≤ a ∧ y ∈ a • subdifferential (pairing n) f x := by
  have hri : x ∈ ri (dom f) := interior_subset_intrinsicInterior hx
  obtain ⟨y₀, hy₀⟩ := theorem_23_4_nonempty hf hp hri
  rw [corollary_23_7_1 hf hp hr hinf hx,
    mem_coe_hull_iff_of_convex (convex_subdifferential (pairing n) f x)]
  constructor
  · rintro (rfl | ⟨t, ht, hmem⟩)
    · exact ⟨0, le_rfl, ⟨y₀, hy₀, by simp⟩⟩
    · exact ⟨t, ht.le, hmem⟩
  · rintro ⟨a, ha, hmem⟩
    rcases eq_or_lt_of_le ha with rfl | ha'
    · obtain ⟨w, -, hw⟩ := hmem
      exact Or.inl (by rw [← hw]; simp)
    · exact Or.inr ⟨a, ha', hmem⟩

/-! ### Theorem 23.8: the sum rule -/

/-- **Theorem 23.8**, the unconditional inclusion: `∂(f₁ + ⋯ + fₘ)(x) ⊇ ∂f₁(x) + ⋯ + ∂fₘ(x)`, with
no hypothesis — the `m` subgradient inequalities simply add. -/
theorem theorem_23_8_subset {ι : Type*} (s : Finset ι) (f : ι → Rn n → EReal) (x : Rn n) :
    ∑ i ∈ s, subdifferential (pairing n) (f i) x ⊆ subdifferential (pairing n) (∑ i ∈ s, f i) x :=
  subdifferential_finsetSum_subset (pairing n) s f x

/-- **Theorem 23.8**. If the sets `ri (dom fᵢ)` have a point in common, then
`∂(f₁ + ⋯ + fₘ)(x) = ∂f₁(x) + ⋯ + ∂fₘ(x)` for every `x`. Stated for a `Finset` of summands, as the
book states it, and **not** by induction on `m`: the constraint qualification is discharged once,
by Theorem 16.4 in the same `m`-ary form. The book's ALTERNATIVE PROOF (p. 220) is more elementary
— proper separation of `{(x, μ) | μ ≥ f₁ x}` from `{(x, μ) | μ ≤ -f₂ x}` in `ℝⁿ⁺¹` — but reduces
`m` to `2` by an induction this route avoids. -/
theorem theorem_23_8 {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {f : ι → Rn n → EReal}
    (hf : ∀ i ∈ s, ConvexFn (f i)) (hpf : ∀ i ∈ s, Proper (f i)) {x₀ : Rn n}
    (hx₀ : ∀ i ∈ s, x₀ ∈ ri (dom (f i))) (x : Rn n) :
    subdifferential (pairing n) (∑ i ∈ s, f i) x = ∑ i ∈ s, subdifferential (pairing n) (f i) x :=
  (IsExactFinsetSum.of_relint hs hf hpf hx₀).subdifferential_finsetSum x

/-- **Theorem 23.8**, last sentence: the condition for equality weakens when some `fᵢ` are
polyhedral. If `f₁, …, f_k` are polyhedral it is enough that `dom f₁, …, dom f_k`,
`ri (dom f_{k+1}), …, ri (dom fₘ)` have a point in common — Theorem 20.1. Here `t` is the book's
`{1, …, k}` and `u` its complement. The book's ALTERNATIVE PROOF does not cover this clause. -/
theorem theorem_23_8_polyhedral {ι : Type*} {s t u : Finset ι} (hs : s.Nonempty)
    (hdisj : Disjoint t u) (hmem : ∀ i, i ∈ s ↔ i ∈ t ∨ i ∈ u) {f : ι → Rn n → EReal}
    (hpoly : ∀ i ∈ t, PolyhedralFn (f i)) (hconv : ∀ i ∈ u, ConvexFn (f i))
    (hpf : ∀ i ∈ s, Proper (f i)) {x₀ : Rn n} (hxt : ∀ i ∈ t, x₀ ∈ dom (f i))
    (hxu : ∀ i ∈ u, x₀ ∈ ri (dom (f i))) (x : Rn n) :
    subdifferential (pairing n) (∑ i ∈ s, f i) x = ∑ i ∈ s, subdifferential (pairing n) (f i) x :=
  (IsExactFinsetSum.of_polyhedral hs hdisj hmem hpoly hconv hpf hxt hxu).subdifferential_finsetSum x

/-! ### Corollary 23.8.1: normals to an intersection -/

private theorem biInter_cons {ι : Type*} {i : ι} {t : Finset ι} (hi : i ∉ t)
    (C : ι → Set (Rn n)) : (⋂ j ∈ Finset.cons i t hi, C j) = C i ∩ ⋂ j ∈ t, C j := by
  ext z
  simp only [Set.mem_iInter, Set.mem_inter_iff, Finset.mem_cons]
  constructor
  · intro hz
    exact ⟨hz i (Or.inl rfl), fun j hj => hz j (Or.inr hj)⟩
  · rintro ⟨h₁, h₂⟩ j (rfl | hj)
    · exact h₁
    · exact h₂ j hj

/-- **Corollary 23.8.1**, the unconditional inclusion: the sum of the normal cones is contained in
the normal cone to the intersection. Proved directly, so no hypothesis is needed. -/
theorem corollary_23_8_1_subset {ι : Type*} (C : ι → Set (Rn n)) (x : Rn n) :
    ∀ s : Finset ι,
      ∑ i ∈ s, normalCone (pairing n) (C i) x ⊆ normalCone (pairing n) (⋂ i ∈ s, C i) x := by
  intro s
  induction s using Finset.cons_induction with
  | empty =>
      intro y hy
      simp only [Finset.sum_empty, Set.mem_zero] at hy
      subst hy
      simp
  | cons i t hi ih =>
      rw [Finset.sum_cons, biInter_cons hi C]
      exact (Set.add_subset_add_left ih).trans (normalCone_add_subset (pairing n) (C i) _ x)

/-- **Corollary 23.8.1**. If the convex sets `C₁, …, Cₘ` have a common relative interior point, the
normal cone to `C₁ ∩ ⋯ ∩ Cₘ` at `x` is the sum of the normal cones to the `Cᵢ` at `x`. This is the
indicator instance of Theorem 23.8. **The hypothesis `x ∈ Cᵢ` is not in the book and is not
removable**: Rockafellar's `N_C(x)` is `∂δ(x | C)`, which is empty off `C`, whereas `normalCone` is
defined everywhere and always contains `0`; the two agree exactly on `C`. -/
theorem corollary_23_8_1 {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {C : ι → Set (Rn n)}
    (hC : ∀ i ∈ s, Convex ℝ (C i)) {x₀ : Rn n} (hx₀ : ∀ i ∈ s, x₀ ∈ ri (C i)) {x : Rn n}
    (hx : ∀ i ∈ s, x ∈ C i) :
    normalCone (pairing n) (⋂ i ∈ s, C i) x = ∑ i ∈ s, normalCone (pairing n) (C i) x := by
  have hconv : ∀ i ∈ s, ConvexFn (indicatorFn (C i)) :=
    fun i hi => convexFn_indicatorFn.2 (hC i hi)
  have hprop : ∀ i ∈ s, Proper (indicatorFn (C i)) := fun i hi =>
    ⟨⟨x, by rw [dom_indicatorFn]; exact hx i hi⟩, indicatorFn_ne_bot (C i)⟩
  have hri : ∀ i ∈ s, x₀ ∈ ri (dom (indicatorFn (C i))) := by
    intro i hi
    rw [dom_indicatorFn]
    exact hx₀ i hi
  have hsum := theorem_23_8 hs hconv hprop hri x
  rw [indicatorFn_finsetSum C s,
    subdifferential_indicatorFn (Set.mem_iInter₂.2 hx)] at hsum
  rw [hsum]
  exact Finset.sum_congr rfl fun i hi => subdifferential_indicatorFn (hx i hi)

/-! ### Theorem 23.9: composition with a linear transformation -/

/-- **Theorem 23.9**, the unconditional inclusion: for `f(x) = h(Ax)`, `∂f(x) ⊇ A*∂h(Ax)`. Here
`h` is arbitrary and only the adjointness is used. -/
theorem theorem_23_9_subset (A : Rn n →ₗ[ℝ] Rn m) (h : Rn m → EReal) (x : Rn n) :
    LinearMap.adjoint A '' subdifferential (pairing m) h (A x)
      ⊆ subdifferential (pairing n) (compLin h A) x :=
  image_subdifferential_subset (isAdjointPair_adjoint A) h x

/-- **Theorem 23.9**. For `f(x) = h(Ax)` with `h` proper convex on `ℝᵐ`: if the range of `A`
contains a point of `ri (dom h)`, then `∂f(x) = A*∂h(Ax)` for every `x`. This is Theorem 23.5
applied to the exact conjugacy formula of Theorem 16.3; Rockafellar's `A*` is
`LinearMap.adjoint A`. -/
theorem theorem_23_9 (A : Rn n →ₗ[ℝ] Rn m) {h : Rn m → EReal} (hh : ConvexFn h) (hp : Proper h)
    {x₀ : Rn n} (hx₀ : A x₀ ∈ ri (dom h)) (x : Rn n) :
    subdifferential (pairing n) (compLin h A) x
      = LinearMap.adjoint A '' subdifferential (pairing m) h (A x) :=
  (IsExactImage.of_relint (isAdjointPair_adjoint A) hh hp hx₀).subdifferential_compLin x

/-- **Theorem 23.9**, last clause: if `h` is *polyhedral* and the range of `A` merely meets
`dom h` — no relative interior — then `∂f(x) = A*∂h(Ax)`. The book's route is Theorem 16.3 via
Corollary 19.3.1, which is the one taken here. -/
theorem theorem_23_9_polyhedral (A : Rn n →ₗ[ℝ] Rn m) {h : Rn m → EReal} (hh : PolyhedralFn h)
    (hp : Proper h) {x₀ : Rn n} (hx₀ : A x₀ ∈ dom h) (x : Rn n) :
    subdifferential (pairing n) (compLin h A) x
      = LinearMap.adjoint A '' subdifferential (pairing m) h (A x) :=
  (IsExactImage.of_polyhedral (isAdjointPair_adjoint A) hh hp hx₀).subdifferential_compLin x

/-! ### Theorem 23.10: the polyhedral case -/

/-- **Theorem 23.10**, first assertion: a polyhedral convex function is subdifferentiable wherever
it is finite. No relative interior is needed: the cone generated by `epi f - (x, f x)` is
polyhedral, hence closed (Corollary 19.7.1), so `f'(x; ·)` is already closed. -/
theorem theorem_23_10_nonempty {f : Rn n → EReal} (hf : PolyhedralFn f) {x : Rn n}
    (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) : (subdifferential (pairing n) f x).Nonempty :=
  subdifferential_nonempty_of_polyhedralFn hf ht hb

/-- **Theorem 23.10**: and `∂f(x)` is a polyhedral convex set. -/
theorem theorem_23_10_polyhedral {f : Rn n → EReal} (hf : PolyhedralFn f) {x : Rn n}
    (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) : Polyhedral (subdifferential (pairing n) f x) :=
  polyhedral_subdifferential_of_polyhedralFn hf ht hb

/-- **Theorem 23.10**: `f'(x; ·)` is a polyhedral convex function. -/
theorem theorem_23_10_dirDeriv_polyhedral {f : Rn n → EReal} (hf : PolyhedralFn f) {x : Rn n}
    (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) : PolyhedralFn (dirDeriv f x) :=
  polyhedralFn_dirDeriv hf ht hb

/-- **Theorem 23.10**: `f'(x; ·)` is proper. The book's reason: `f'(x; 0) = 0`, and a polyhedral
convex function taking the value `-∞` somewhere has no finite values at all. -/
theorem theorem_23_10_dirDeriv_proper {f : Rn n → EReal} (hf : PolyhedralFn f) {x : Rn n}
    (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) : Proper (dirDeriv f x) :=
  proper_dirDeriv_of_polyhedralFn hf ht hb

/-- **Theorem 23.10**, last assertion: `f'(x; ·)` is the support function of `∂f(x)`, with no
closure operation. -/
theorem theorem_23_10_supportFn {f : Rn n → EReal} (hf : PolyhedralFn f) {x : Rn n}
    (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) :
    dirDeriv f x = supportFn (pairing n) (subdifferential (pairing n) f x) := by
  have h := dirDeriv_eq_supportFn_of_polyhedralFn (B := pairing n) hf ht hb
  rwa [flip_pairing] at h

end Rockafellar
