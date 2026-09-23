import Numlib.Analysis.Convex.Line
import Numlib.Analysis.Convex.Saddle.Continuity
import Numlib.Analysis.Convex.Subdifferential.Convergence
import Numlib.Analysis.Convex.Subdifferential.Gradient

/-!
# Directional derivatives and subgradients of a saddle-function

The one-variable differential theory of convex functions, read for a concave-convex function of a
pair on an open rectangle `C ×ˢ D` where the function is finite and real-valued.

The joint one-sided directional derivative exists and splits,
`K'(u, v; u', v') = K'(u, v; u', 0) + K'(u, v; 0, v')`, and is a finite concave-convex function of
the direction. The subdifferential `∂K = ∂₁K ×ˢ ∂₂K` is a *product* — the two variables never
interact — so differentiability is a *separate* condition in each variable: `K` is differentiable
at a point exactly when `∂K` is a singleton there. The directional derivatives are semicontinuous
and `∂K` upper semicontinuous along a convergent sequence.

## Main definitions

* `dirDerivReal f x y` — the one-sided directional derivative `f'(x; y)` of a real-valued function,
  read as a genuine limit and taking the junk value `0` where that limit fails to exist.
* `superdifferentialFstOn`, `subdifferentialSndOn`, `saddleSubdifferentialOn` — `∂₁K`, `∂₂K` and
  `∂K = ∂₁K ×ˢ ∂₂K`.
* `prodInnerL q` — the functional `(w, x) ↦ ⟪w, q.1⟫ + ⟪x, q.2⟫` that a pair represents;
  `HasSaddleGradientAt K q p` is `HasFDerivAt K (prodInnerL q) p`.

## Main results

* `dirDerivReal_prod`, `tendsto_slope_dirDerivReal_prod`, `concaveConvexOn_dirDerivReal` — the
  joint limit exists, splits into the two partial derivatives, and is a finite concave-convex
  function of the direction ([rockafellar1970convex] Theorem 35.6).
* `eventually_dirDerivReal_snd_lt`, `eventually_lt_dirDerivReal_fst`,
  `eventually_saddleSubdifferentialOn_subset` — the two semicontinuity inequalities, spelled without
  junk values, and `∂K_i(u_i, v_i) ⊆ ∂K(u, v) + εB` eventually
  ([rockafellar1970convex] Theorem 35.7).
* `lowerSemicontinuousAt_dirDerivReal_fst`, `upperSemicontinuousAt_dirDerivReal_snd`,
  `eventually_nhds_saddleSubdifferentialOn_subset` — the same for the constant sequence, that is,
  plain semicontinuity on the rectangle.
* `hasSaddleGradientAt_iff_saddleSubdifferentialOn_eq_singleton`,
  `differentiableAt_iff_exists_saddleSubdifferentialOn_eq_singleton` — differentiability is unique
  subdifferentiability ([rockafellar1970convex] Theorem 35.8).
* `differentiableAt_iff_isLinearMap_dirDerivReal` — where `K` is already finite, differentiability
  is exactly linearity of `K'(u, v; ·, ·)`.

Four one-variable statements are proved here in real form, because the `EReal` versions are not
usable through a slice without a detour: the gradient inequality and its uniqueness half, the
description of `∂f(x)` by the directional derivative at an interior point, and nonemptiness of
`∂f(x)` there. Each concave mirror is the convex statement for `-f`, through
`dirDerivReal_neg_of_tendsto`; each statement about the concave variable of a saddle-function is
the one about the convex variable read at `swapReal K`, through
`superdifferentialFstOn_eq_neg_subdifferentialSndOn_swapReal`.

## Implementation notes

`superdifferentialFstOn` and `subdifferentialSndOn` test against `C` and `D` rather than the whole
space; Rockafellar tests against `Rᵐ`, the case `C = univ`, and the two agree once `K` is extended
off the rectangle by the simple extension of `Saddle/Kernel.lean`.

Mathlib gives `U × X` the *supremum* norm, so it is not an inner-product space and `∇K (u, v)` has
to be a pair rather than a vector; the same choice makes the `εB` of the semicontinuity statements
the supremum ball rather than the book's Euclidean one, harmlessly, since every statement
quantifies over all `ε > 0`. Everything is stated on an *open* rectangle, as in the book.

## References

* [rockafellar1970convex] §35.
-/

open Set Filter Topology
open scoped Pointwise RealInnerProductSpace

namespace ConvexAnalysis

/-! ### The one-sided directional derivative of a real-valued function -/

section DirDerivReal

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {S : Set E} {f : E → ℝ} {x y : E}

/-- The **one-sided directional derivative** `f'(x; y)` of a real-valued function: the limit of the
difference quotient as the step decreases to `0`, with the junk value `0` where it does not exist.

`dirDeriv` (`Subdifferential/Defs.lean`) is an infimum instead, which agrees with the limit only
when the quotient is monotone in the step — true along a line for a convex function, false for a
saddle-function in a joint direction, which is the case treated here. -/
noncomputable def dirDerivReal (f : E → ℝ) (x y : E) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) fun t => (f (x + t • y) - f x) / t

/-- Reading off `dirDerivReal` from a limit that is known to exist. -/
theorem dirDerivReal_eq_of_tendsto {L : ℝ}
    (h : Tendsto (fun t : ℝ => (f (x + t • y) - f x) / t) (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    dirDerivReal f x y = L :=
  h.limUnder_eq

/-- **At a point where a convex function is finite on a neighbourhood, the one-sided difference
quotient converges.** It is the secant slope along the line `t ↦ x + t • y`, nondecreasing and
bounded below by its value at a negative step, so it converges to its infimum. -/
theorem exists_tendsto_slope_of_convexOn [TopologicalSpace E] [ContinuousAdd E]
    [ContinuousSMul ℝ E] (hS : IsOpen S) (hf : ConvexOn ℝ S f) (hx : x ∈ S) (y : E) :
    ∃ L : ℝ, Tendsto (fun t : ℝ => (f (x + t • y) - f x) / t) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  have hIopen : IsOpen {t : ℝ | x + t • y ∈ S} := isOpen_line_steps hS x y
  have h0 : (0 : ℝ) ∈ {t : ℝ | x + t • y ∈ S} := by simpa using hx
  have hg : ConvexOn ℝ {t : ℝ | x + t • y ∈ S} fun t => f (x + t • y) := convexOn_comp_line hf x y
  obtain ⟨δ, hδ, hsub⟩ : ∃ δ : ℝ, 0 < δ ∧ Ioo (-δ) δ ⊆ {t : ℝ | x + t • y ∈ S} := by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hIopen 0 h0
    refine ⟨ε, hε, fun t ht => hball ?_⟩
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact ⟨ht.1, ht.2⟩
  have hx0 : f (x + (0 : ℝ) • y) = f x := by simp
  have hsec : ∀ s ∈ {t : ℝ | x + t • y ∈ S}, ∀ t ∈ {t : ℝ | x + t • y ∈ S}, s ≠ 0 → t ≠ 0 →
      s ≤ t → (f (x + s • y) - f x) / s ≤ (f (x + t • y) - f x) / t := by
    intro s hs t ht hs0 ht0 hst
    simpa [hx0] using hg.secant_mono h0 hs ht hs0 ht0 hst
  have hmono : MonotoneOn (fun t : ℝ => (f (x + t • y) - f x) / t) (Ioo 0 δ) := by
    intro s hs t ht hst
    exact hsec s (hsub ⟨by linarith [hs.1], hs.2⟩) t (hsub ⟨by linarith [ht.1], ht.2⟩)
      (ne_of_gt hs.1) (ne_of_gt ht.1) hst
  have hbdd : BddBelow ((fun t : ℝ => (f (x + t • y) - f x) / t) '' Ioo 0 δ) := by
    refine ⟨(f (x + (-δ / 2) • y) - f x) / (-δ / 2), ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact hsec (-δ / 2) (hsub ⟨by linarith, by linarith⟩) t (hsub ⟨by linarith [ht.1], ht.2⟩)
      (by linarith) (ne_of_gt ht.1) (by linarith [ht.1])
  exact ⟨_, MonotoneOn.tendsto_nhdsWithin_Ioo_right (Set.nonempty_Ioo.2 hδ) hmono hbdd⟩

/-- The same for a concave function: the one-sided difference quotient converges. -/
theorem exists_tendsto_slope_of_concaveOn [TopologicalSpace E] [ContinuousAdd E]
    [ContinuousSMul ℝ E] (hS : IsOpen S) (hf : ConcaveOn ℝ S f) (hx : x ∈ S) (y : E) :
    ∃ L : ℝ, Tendsto (fun t : ℝ => (f (x + t • y) - f x) / t) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  obtain ⟨L, hL⟩ := exists_tendsto_slope_of_convexOn hS hf.neg hx y
  refine ⟨-L, ?_⟩
  refine hL.neg.congr fun t => ?_
  simp only [Pi.neg_apply]
  ring

/-- The difference quotient of a convex function converges to `dirDerivReal`. -/
theorem tendsto_slope_dirDerivReal_of_convexOn [TopologicalSpace E] [ContinuousAdd E]
    [ContinuousSMul ℝ E] (hS : IsOpen S) (hf : ConvexOn ℝ S f) (hx : x ∈ S) (y : E) :
    Tendsto (fun t : ℝ => (f (x + t • y) - f x) / t) (𝓝[>] (0 : ℝ)) (𝓝 (dirDerivReal f x y)) := by
  obtain ⟨L, hL⟩ := exists_tendsto_slope_of_convexOn hS hf hx y
  rwa [dirDerivReal_eq_of_tendsto hL]

/-- The difference quotient of a concave function converges to `dirDerivReal`. -/
theorem tendsto_slope_dirDerivReal_of_concaveOn [TopologicalSpace E] [ContinuousAdd E]
    [ContinuousSMul ℝ E] (hS : IsOpen S) (hf : ConcaveOn ℝ S f) (hx : x ∈ S) (y : E) :
    Tendsto (fun t : ℝ => (f (x + t • y) - f x) / t) (𝓝[>] (0 : ℝ)) (𝓝 (dirDerivReal f x y)) := by
  obtain ⟨L, hL⟩ := exists_tendsto_slope_of_concaveOn hS hf hx y
  rwa [dirDerivReal_eq_of_tendsto hL]

/-- **Positive homogeneity, in the form that transports a limit.** No convexity is involved: it is
the reparametrisation `t ↦ t * c` of the difference quotient. -/
theorem tendsto_slope_smul {c : ℝ} (hc : 0 < c) {L : ℝ}
    (h : Tendsto (fun t : ℝ => (f (x + t • y) - f x) / t) (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    Tendsto (fun t : ℝ => (f (x + t • (c • y)) - f x) / t) (𝓝[>] (0 : ℝ)) (𝓝 (c * L)) := by
  have hmap : Tendsto (fun t : ℝ => t * c) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using ((continuous_mul_const c).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_pos ht hc
  refine ((h.comp hmap).const_mul c).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [Function.comp_apply, smul_smul]
  field_simp

/-- Positive homogeneity of `f'(x; ·)`, wherever the limit defining it exists. -/
theorem dirDerivReal_smul_of_tendsto {c : ℝ} (hc : 0 < c) {L : ℝ}
    (h : Tendsto (fun t : ℝ => (f (x + t • y) - f x) / t) (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    dirDerivReal f x (c • y) = c * dirDerivReal f x y := by
  rw [dirDerivReal_eq_of_tendsto h, dirDerivReal_eq_of_tendsto (tendsto_slope_smul hc h)]

/-- `f'(x; 0) = 0`, with no hypothesis: the difference quotient is identically `0`. -/
theorem dirDerivReal_zero (f : E → ℝ) (x : E) : dirDerivReal f x 0 = 0 :=
  dirDerivReal_eq_of_tendsto (by simp)

/-- `(-f)'(x; y) = -f'(x; y)` wherever the limit defining `f'(x; y)` exists. The hypothesis cannot
be dropped: off it `dirDerivReal` is a junk value that negation need not respect. This is how
every concave statement below is read off its convex twin. -/
theorem dirDerivReal_neg_of_tendsto {L : ℝ}
    (h : Tendsto (fun t : ℝ => (f (x + t • y) - f x) / t) (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    dirDerivReal (-f) x y = -dirDerivReal f x y := by
  rw [dirDerivReal_eq_of_tendsto h]
  refine dirDerivReal_eq_of_tendsto (h.neg.congr fun t => ?_)
  simp only [Pi.neg_apply]
  ring

end DirDerivReal

/-! ### Convexity of the directional derivative in the direction -/

section DirDerivConvex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousAdd E]
  [ContinuousSMul ℝ E] {S : Set E} {f : E → ℝ} {x : E}

omit [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E] in
/-- The affine identity behind every restriction to a line: for `a + b = 1` the point
`x + t • (a • d₁ + b • d₂)` is the corresponding convex combination of `x + t • d₁` and
`x + t • d₂`. -/
theorem add_smul_convexComb (x d₁ d₂ : E) {a b : ℝ} (hab : a + b = 1) (t : ℝ) :
    x + t • (a • d₁ + b • d₂) = a • (x + t • d₁) + b • (x + t • d₂) := by
  match_scalars
  · linarith
  · ring
  · ring

/-- Every direction eventually stays inside an open set. -/
theorem eventually_nhdsGT_add_smul_mem (hS : IsOpen S) (hx : x ∈ S) (y : E) :
    ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), x + t • y ∈ S :=
  nhdsWithin_le_nhds ((isOpen_line_steps hS x y).mem_nhds (by simpa using hx))

/-- **`f'(x; ·)` is a convex function of the direction** on the whole space, when `f` is convex on
an open set containing `x`.

The difference quotient is convex in the direction for every fixed step, by the affine identity
`add_smul_convexComb` together with the convexity of `f`; the inequality survives the limit. -/
theorem convexOn_dirDerivReal (hS : IsOpen S) (hf : ConvexOn ℝ S f) (hx : x ∈ S) :
    ConvexOn ℝ (univ : Set E) (dirDerivReal f x) := by
  refine ⟨convex_univ, fun y₁ _ y₂ _ a b ha hb hab => ?_⟩
  refine le_of_tendsto_of_tendsto
    (tendsto_slope_dirDerivReal_of_convexOn hS hf hx (a • y₁ + b • y₂))
    (((tendsto_slope_dirDerivReal_of_convexOn hS hf hx y₁).const_mul a).add
      ((tendsto_slope_dirDerivReal_of_convexOn hS hf hx y₂).const_mul b)) ?_
  filter_upwards [self_mem_nhdsWithin, eventually_nhdsGT_add_smul_mem hS hx y₁,
    eventually_nhdsGT_add_smul_mem hS hx y₂] with t ht ht₁ ht₂
  have ht' : (0 : ℝ) < t := ht
  have hle : f (x + t • (a • y₁ + b • y₂)) ≤ a * f (x + t • y₁) + b * f (x + t • y₂) := by
    rw [add_smul_convexComb x y₁ y₂ hab t]
    simpa using hf.2 ht₁ ht₂ ha hb hab
  have hsum : a * ((f (x + t • y₁) - f x) / t) + b * ((f (x + t • y₂) - f x) / t)
      = (a * f (x + t • y₁) + b * f (x + t • y₂) - f x) / t := by
    field_simp
    linear_combination (-(f x)) * hab
  simp only [hsum]
  gcongr

/-- The mirror: `f'(x; ·)` is a concave function of the direction. It is the convex statement for
`-f`, whose directional derivative is `-f'(x; ·)`. -/
theorem concaveOn_dirDerivReal (hS : IsOpen S) (hf : ConcaveOn ℝ S f) (hx : x ∈ S) :
    ConcaveOn ℝ (univ : Set E) (dirDerivReal f x) := by
  refine (convexOn_dirDerivReal hS hf.neg hx).neg.congr fun y _ => ?_
  rw [Pi.neg_apply, dirDerivReal_neg_of_tendsto
    (tendsto_slope_dirDerivReal_of_concaveOn hS hf hx y), neg_neg]

/-- **The directional derivative of a convex function is bounded above by *every* difference
quotient** whose step keeps the point inside the set on which `f` is convex.

The quotient is nondecreasing in the step, so the limit at `0` is below the value at step `α`. -/
theorem dirDerivReal_le_slope {y : E} (hS : IsOpen S) (hf : ConvexOn ℝ S f) (hx : x ∈ S) {α : ℝ}
    (hα : 0 < α) (hxα : x + α • y ∈ S) :
    dirDerivReal f x y ≤ (f (x + α • y) - f x) / α := by
  refine le_of_tendsto (tendsto_slope_dirDerivReal_of_convexOn hS hf hx y) ?_
  filter_upwards [eventually_nhdsGT_add_smul_mem hS hx y, self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds hα)] with t ht htpos htα
  have h0 : (0 : ℝ) ∈ {t : ℝ | x + t • y ∈ S} := by simpa using hx
  have hsec := (convexOn_comp_line hf x y).secant_mono h0 ht hxα
    (ne_of_gt (show (0 : ℝ) < t from htpos)) (ne_of_gt hα) (le_of_lt htα)
  simpa using hsec

/-- The concave counterpart of `dirDerivReal_le_slope`, read off it for `-f`. -/
theorem slope_le_dirDerivReal {y : E} (hS : IsOpen S) (hf : ConcaveOn ℝ S f) (hx : x ∈ S) {α : ℝ}
    (hα : 0 < α) (hxα : x + α • y ∈ S) :
    (f (x + α • y) - f x) / α ≤ dirDerivReal f x y := by
  have h := dirDerivReal_le_slope hS hf.neg hx hα hxα
  rw [dirDerivReal_neg_of_tendsto (tendsto_slope_dirDerivReal_of_concaveOn hS hf hx y)] at h
  simp only [Pi.neg_apply] at h
  rw [show (-f (x + α • y) - -f x) / α = -((f (x + α • y) - f x) / α) by ring] at h
  exact neg_le_neg_iff.1 h

end DirDerivConvex

/-! ### The joint directional derivative of a saddle-function -/

section Saddle

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [TopologicalSpace U] [ContinuousAdd U]
  [ContinuousSMul ℝ U] [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] [ContinuousAdd X]
  [ContinuousSMul ℝ X] {C : Set U} {D : Set X} {K : U × X → ℝ} {u : U} {v : X}

/-- **The `limsup` half**: moving the concave variable does not raise the difference quotient of
the convex variable above its limit at the base point.

Given `μ` above `K'(u, v; 0, v')`, some step `α > 0` already realises a secant slope of the convex
slice below `μ`; the concave slice is continuous along `t ↦ u + t • u'`, so the same secant slope at
the moving point is still below `μ` for small `t`. -/
theorem eventually_slope_snd_lt (hCo : IsOpen C) (hDo : IsOpen D) (hK : ConcaveConvexOn C D K)
    (hu : u ∈ C) (hv : v ∈ D) {u' : U} {v' : X} {b μ : ℝ}
    (hb : Tendsto (fun t : ℝ => (K (u, v + t • v') - K (u, v)) / t) (𝓝[>] (0 : ℝ)) (𝓝 b))
    (hμ : b < μ) :
    ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      (K (u + t • u', v + t • v') - K (u + t • u', v)) / t < μ := by
  have hJ : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), v + s • v' ∈ D :=
    eventually_nhdsGT_add_smul_mem hDo hv v'
  obtain ⟨α, hαlt, hαJ, hα0⟩ : ∃ α : ℝ, (K (u, v + α • v') - K (u, v)) / α < μ ∧
      v + α • v' ∈ D ∧ 0 < α :=
    ((hb.eventually_lt_const hμ).and (hJ.and self_mem_nhdsWithin)).exists.imp
      fun _ h => ⟨h.1, h.2.1, h.2.2⟩
  have hcont : ContinuousAt
      (fun t : ℝ => (K (u + t • u', v + α • v') - K (u + t • u', v)) / α) 0 :=
    ((continuousAt_comp_line_of_concaveOn hCo (hK.concave_fst _ hαJ) hu u').sub
      (continuousAt_comp_line_of_concaveOn hCo (hK.concave_fst v hv) hu u')).div_const α
  have hΦ : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      (K (u + t • u', v + α • v') - K (u + t • u', v)) / α < μ := by
    refine nhdsWithin_le_nhds (hcont.eventually_lt_const ?_)
    simpa using hαlt
  filter_upwards [hΦ, eventually_nhdsGT_add_smul_mem hCo hu u', hJ,
    nhdsWithin_le_nhds (Iio_mem_nhds hα0), self_mem_nhdsWithin] with t hΦt hIt hJt hlt ht
  have h0 : (0 : ℝ) ∈ {s : ℝ | v + s • v' ∈ D} := by simpa using hv
  have hsec := (convexOn_comp_line (hK.convex_snd _ hIt) v v').secant_mono h0 hJt hαJ
    (ne_of_gt (show (0 : ℝ) < t from ht)) (ne_of_gt hα0) (le_of_lt hlt)
  simp only [zero_smul, add_zero, sub_zero] at hsec
  exact lt_of_le_of_lt hsec hΦt

/-- **The joint one-sided directional derivative of a finite concave-convex function at an interior
point of the rectangle exists**, and it is the *sum* of the two partial directional derivatives.

The difference quotient splits as
`[K(u + t u', v) - K(u, v)]/t + [K(u + t u', v + t v') - K(u + t u', v)]/t`, whose first summand
converges by the one-variable existence clause. `eventually_slope_snd_lt` bounds the second above
by anything above `K'(u, v; 0, v')`, and the matching lower bound is that lemma at the negated
swap. -/
theorem tendsto_slope_prod (hCo : IsOpen C) (hDo : IsOpen D) (hK : ConcaveConvexOn C D K)
    (hu : u ∈ C) (hv : v ∈ D) {u' : U} {v' : X} {a b : ℝ}
    (ha : Tendsto (fun t : ℝ => (K (u + t • u', v) - K (u, v)) / t) (𝓝[>] (0 : ℝ)) (𝓝 a))
    (hb : Tendsto (fun t : ℝ => (K (u, v + t • v') - K (u, v)) / t) (𝓝[>] (0 : ℝ)) (𝓝 b)) :
    Tendsto (fun t : ℝ => (K (u + t • u', v + t • v') - K (u, v)) / t) (𝓝[>] (0 : ℝ))
      (𝓝 (a + b)) := by
  rw [tendsto_order]
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · obtain ⟨ε, hε, rfl⟩ : ∃ ε : ℝ, 0 < ε ∧ c = a + b - 2 * ε :=
      ⟨(a + b - c) / 2, by linarith, by ring⟩
    have hswapb : Tendsto (fun t : ℝ => (-K (u + t • u', v) - -K (u, v)) / t)
        (𝓝[>] (0 : ℝ)) (𝓝 (-a)) := ha.neg.congr fun t => by ring
    have hswap := eventually_slope_snd_lt (K := swapReal K)
      (u' := v') (v' := u') (b := -a) (μ := -(a - ε)) hDo hCo hK.swapReal hv hu hswapb
      (by linarith)
    filter_upwards [hswap, hb.eventually_const_lt (show b - ε < b by linarith)] with t h₁ h₂
    have h₁' : (-K (u + t • u', v + t • v') - -K (u, v + t • v')) / t < -(a - ε) := h₁
    have heq : (-K (u + t • u', v + t • v') - -K (u, v + t • v')) / t
        = -((K (u + t • u', v + t • v') - K (u, v + t • v')) / t) := by ring
    rw [heq] at h₁'
    have hsplit : (K (u + t • u', v + t • v') - K (u, v)) / t
        = (K (u, v + t • v') - K (u, v)) / t
          + (K (u + t • u', v + t • v') - K (u, v + t • v')) / t := by ring
    rw [hsplit]
    linarith
  · obtain ⟨ε, hε, rfl⟩ : ∃ ε : ℝ, 0 < ε ∧ c = a + b + 2 * ε :=
      ⟨(c - (a + b)) / 2, by linarith, by ring⟩
    have hsnd := eventually_slope_snd_lt (u' := u') hCo hDo hK hu hv hb
      (show b < b + ε by linarith)
    filter_upwards [hsnd, ha.eventually_lt_const (show a < a + ε by linarith)] with t h₁ h₂
    have hsplit : (K (u + t • u', v + t • v') - K (u, v)) / t
        = (K (u + t • u', v) - K (u, v)) / t
          + (K (u + t • u', v + t • v') - K (u + t • u', v)) / t := by ring
    rw [hsplit]
    linarith

end Saddle

/-! ### The joint directional derivative in terms of `dirDerivReal` -/

section SaddleDirDeriv

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [TopologicalSpace U] [ContinuousAdd U]
  [ContinuousSMul ℝ U] [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] [ContinuousAdd X]
  [ContinuousSMul ℝ X] {C : Set U} {D : Set X} {K : U × X → ℝ} {u : U} {v : X}

/-- The joint difference quotient of a finite concave-convex function converges, and its limit is
`dirDerivReal K (u, v) q`.

This is `tendsto_slope_prod` with the two partial limits supplied by
`tendsto_slope_dirDerivReal_of_concaveOn` and `..._of_convexOn`. -/
theorem tendsto_slope_dirDerivReal_prod (hCo : IsOpen C) (hDo : IsOpen D)
    (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D) (q : U × X) :
    Tendsto (fun t : ℝ => (K ((u, v) + t • q) - K (u, v)) / t) (𝓝[>] (0 : ℝ))
      (𝓝 (dirDerivReal (fun w => K (w, v)) u q.1 + dirDerivReal (fun x => K (u, x)) v q.2)) :=
  tendsto_slope_prod hCo hDo hK hu hv
    (tendsto_slope_dirDerivReal_of_concaveOn hCo (hK.concave_fst v hv) hu q.1)
    (tendsto_slope_dirDerivReal_of_convexOn hDo (hK.convex_snd u hu) hv q.2)

/-- The splitting of the joint directional derivative:
`K'(u, v; u', v') = K'(u, v; u', 0) + K'(u, v; 0, v')`. -/
theorem dirDerivReal_prod (hCo : IsOpen C) (hDo : IsOpen D) (hK : ConcaveConvexOn C D K)
    (hu : u ∈ C) (hv : v ∈ D) (q : U × X) :
    dirDerivReal K (u, v) q
      = dirDerivReal (fun w => K (w, v)) u q.1 + dirDerivReal (fun x => K (u, x)) v q.2 :=
  dirDerivReal_eq_of_tendsto (tendsto_slope_dirDerivReal_prod hCo hDo hK hu hv q)

/-- **`K'(u, v; ·, ·)` is a *finite* concave-convex function** on the whole of `U × X`.

By the splitting it is the sum of a concave function of the first direction and a convex function
of the second, and each summand is finite because the corresponding slice of `K` is finite on a
neighbourhood of the base point. -/
theorem concaveConvexOn_dirDerivReal (hCo : IsOpen C) (hDo : IsOpen D)
    (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D) :
    ConcaveConvexOn (univ : Set U) (univ : Set X) (dirDerivReal K (u, v)) := by
  constructor
  · intro q₂ _
    have heq : (fun q₁ : U => dirDerivReal K (u, v) (q₁, q₂))
        = fun q₁ : U => dirDerivReal (fun w => K (w, v)) u q₁
            + dirDerivReal (fun x => K (u, x)) v q₂ :=
      funext fun q₁ => dirDerivReal_prod hCo hDo hK hu hv (q₁, q₂)
    rw [heq]
    exact (concaveOn_dirDerivReal hCo (hK.concave_fst v hv) hu).add_const _
  · intro q₁ _
    have heq : (fun q₂ : X => dirDerivReal K (u, v) (q₁, q₂))
        = fun q₂ : X => dirDerivReal (fun x => K (u, x)) v q₂
            + dirDerivReal (fun w => K (w, v)) u q₁ :=
      funext fun q₂ => by
        rw [dirDerivReal_prod hCo hDo hK hu hv (q₁, q₂)]
        ring
    rw [heq]
    exact (convexOn_dirDerivReal hDo (hK.convex_snd u hu) hv).add_const _

/-- The homogeneity clause: `K'(u, v; ·, ·)` is positively homogeneous. -/
theorem dirDerivReal_prod_smul (hCo : IsOpen C) (hDo : IsOpen D) (hK : ConcaveConvexOn C D K)
    (hu : u ∈ C) (hv : v ∈ D) {c : ℝ} (hc : 0 < c) (q : U × X) :
    dirDerivReal K (u, v) (c • q) = c * dirDerivReal K (u, v) q :=
  dirDerivReal_smul_of_tendsto hc (tendsto_slope_dirDerivReal_prod hCo hDo hK hu hv q)

/-- Read on the first axis: the joint directional derivative in a direction of the form `(u', 0)`
is the partial one, `K'(u, v; u', 0)`. -/
theorem dirDerivReal_prod_fst (hCo : IsOpen C) (hDo : IsOpen D) (hK : ConcaveConvexOn C D K)
    (hu : u ∈ C) (hv : v ∈ D) (u' : U) :
    dirDerivReal K (u, v) (u', 0) = dirDerivReal (fun w => K (w, v)) u u' := by
  rw [dirDerivReal_prod hCo hDo hK hu hv (u', 0)]
  simp [dirDerivReal_zero]

/-- Read on the second axis: the joint derivative at `(0, v')` is `K'(u, v; 0, v')`. -/
theorem dirDerivReal_prod_snd (hCo : IsOpen C) (hDo : IsOpen D) (hK : ConcaveConvexOn C D K)
    (hu : u ∈ C) (hv : v ∈ D) (v' : X) :
    dirDerivReal K (u, v) (0, v') = dirDerivReal (fun x => K (u, x)) v v' := by
  rw [dirDerivReal_prod hCo hDo hK hu hv (0, v')]
  simp [dirDerivReal_zero]

end SaddleDirDeriv

/-! ### The subdifferential of a saddle-function -/

section SubdifferentialDefs

variable {U X : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] {C : Set U} {D : Set X} {K : U × X → ℝ}
  {p : U × X}

/-- `∂₁K(u, v)`, the subdifferential of a saddle-function in its **concave** variable: the
supergradients at `u` of the concave slice `K (·, v)`, tested against the points of `C`.
Rockafellar tests against all of `Rᵐ`, which is the case `C = univ`. -/
def superdifferentialFstOn (C : Set U) (K : U × X → ℝ) (p : U × X) : Set U :=
  {y | ∀ w ∈ C, K (w, p.2) ≤ K p + ⟪w - p.1, y⟫}

/-- `∂₂K(u, v)`: the subgradients at `v` of the convex slice `K (u, ·)`, tested against `D`. -/
def subdifferentialSndOn (D : Set X) (K : U × X → ℝ) (p : U × X) : Set X :=
  {y | ∀ x ∈ D, K p + ⟪x - p.2, y⟫ ≤ K (p.1, x)}

/-- `∂K(u, v) = ∂₁K(u, v) × ∂₂K(u, v)`, Rockafellar's subdifferential of a saddle-function.

It is a *product*, not a set of joint subgradients: the two variables never interact, which is
what makes differentiability a condition on each variable separately. -/
def saddleSubdifferentialOn (C : Set U) (D : Set X) (K : U × X → ℝ) (p : U × X) : Set (U × X) :=
  superdifferentialFstOn C K p ×ˢ subdifferentialSndOn D K p

omit [NormedAddCommGroup X] [InnerProductSpace ℝ X] in
@[simp] theorem mem_superdifferentialFstOn {y : U} :
    y ∈ superdifferentialFstOn C K p ↔ ∀ w ∈ C, K (w, p.2) ≤ K p + ⟪w - p.1, y⟫ := Iff.rfl

omit [NormedAddCommGroup U] [InnerProductSpace ℝ U] in
@[simp] theorem mem_subdifferentialSndOn {y : X} :
    y ∈ subdifferentialSndOn D K p ↔ ∀ x ∈ D, K p + ⟪x - p.2, y⟫ ≤ K (p.1, x) := Iff.rfl

@[simp] theorem mem_saddleSubdifferentialOn {q : U × X} :
    q ∈ saddleSubdifferentialOn C D K p
      ↔ q.1 ∈ superdifferentialFstOn C K p ∧ q.2 ∈ subdifferentialSndOn D K p := Iff.rfl

omit [NormedAddCommGroup U] [InnerProductSpace ℝ U] in
/-- `∂₂K(u, v)` is the subdifferential, in the sense of `Subdifferential/Defs.lean`, of the convex
slice extended by `+∞` off `D`. This is the bridge that lets the one-variable subgradient theory be
applied to a saddle-function one variable at a time. -/
theorem subdifferentialSndOn_eq_subdifferential (hp : p.2 ∈ D) :
    subdifferentialSndOn D K p
      = subdifferential (innerₗ X)
          (ConvexAnalysis.convexRestrict D fun x => ((K (p.1, x) : ℝ) : EReal))
        p.2 := by
  ext y
  simp only [mem_subdifferentialSndOn, mem_subdifferential, convexRestrict_of_mem hp]
  refine ⟨fun h z => ?_, fun h x hx => ?_⟩
  · by_cases hz : z ∈ D
    · rw [convexRestrict_of_mem hz]
      exact_mod_cast h z hz
    · rw [convexRestrict_of_notMem hz]
      exact le_top
  · have hx' := h x
    rw [convexRestrict_of_mem hx] at hx'
    exact_mod_cast hx'

omit [NormedAddCommGroup X] [InnerProductSpace ℝ X] in
/-- **The swap dictionary for subgradients**: `∂₁K(u, v)` is the negated `∂₂` of `swapReal K` at the
swapped point. The supergradient inequality of the concave slice is the subgradient inequality of
the negated slice, which is the convex slice of `swapReal K`. -/
theorem superdifferentialFstOn_eq_neg_subdifferentialSndOn_swapReal :
    superdifferentialFstOn C K p = -subdifferentialSndOn C (swapReal K) p.swap := by
  ext y
  simp only [mem_superdifferentialFstOn, Set.mem_neg, mem_subdifferentialSndOn, swapReal_apply,
    Prod.fst_swap, Prod.snd_swap, inner_neg_right]
  exact forall₂_congr fun w _ => by constructor <;> intro h <;> linarith

omit [NormedAddCommGroup X] [InnerProductSpace ℝ X] in
/-- `∂₁K(u, v)` is the *negated* subdifferential of the negated concave slice extended by `+∞` off
`C`: the concave variable reaches the convex theory through `-K`. -/
theorem superdifferentialFstOn_eq_neg_subdifferential (hp : p.1 ∈ C) :
    superdifferentialFstOn C K p
      = -subdifferential (innerₗ U)
        (ConvexAnalysis.convexRestrict C fun w => ((-K (w, p.2) : ℝ) : EReal)) p.1 := by
  rw [superdifferentialFstOn_eq_neg_subdifferentialSndOn_swapReal,
    subdifferentialSndOn_eq_subdifferential (K := swapReal K) (p := p.swap) hp]
  rfl

end SubdifferentialDefs

/-! ### Continuous convergence, and semicontinuity of the directional derivatives -/

section Convergence

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  {C : Set U} {D : Set X} {Ks : ℕ → U × X → ℝ} {K : U × X → ℝ} {u : U} {v : X}
  {us : ℕ → U} {vs : ℕ → X}

/-- **Finite concave-convex functions converge continuously.** Pointwise convergence on an open
convex rectangle `C × D` forces `K i (u i, v i) → K (u, v)` along every sequence
`(u i, v i) → (u, v)` in `C × D`. This combines uniform convergence on compact rectangles with
continuity of the limit, on a closed-ball rectangle. -/
theorem tendsto_eval_prod_of_tendsto (hCo : IsOpen C) (hCc : Convex ℝ C) (hDo : IsOpen D)
    (hDc : Convex ℝ D) (hKs : ∀ i, ConcaveConvexOn C D (Ks i)) (hK : ConcaveConvexOn C D K)
    (hconv : ∀ q ∈ C ×ˢ D, Tendsto (fun i => Ks i q) atTop (𝓝 (K q)))
    (hu : u ∈ C) (hv : v ∈ D) (hus : Tendsto us atTop (𝓝 u)) (hvs : Tendsto vs atTop (𝓝 v)) :
    Tendsto (fun i => Ks i (us i, vs i)) atTop (𝓝 (K (u, v))) := by
  have hriC : C ⊆ ri C := fun z hz =>
    Convex.interior_subset_relint hCc ⟨u, by rwa [hCo.interior_eq]⟩ (by rwa [hCo.interior_eq])
  have hriD : D ⊆ ri D := fun z hz =>
    Convex.interior_subset_relint hDc ⟨v, by rwa [hDo.interior_eq]⟩ (by rwa [hDo.interior_eq])
  obtain ⟨r, hr, hrball⟩ := Metric.isOpen_iff.1 hCo u hu
  obtain ⟨r', hr', hrball'⟩ := Metric.isOpen_iff.1 hDo v hv
  have hSC : Metric.closedBall u (r / 2) ⊆ C := fun z hz =>
    hrball (Metric.closedBall_subset_ball (by linarith) hz)
  have hTD : Metric.closedBall v (r' / 2) ⊆ D := fun z hz =>
    hrball' (Metric.closedBall_subset_ball (by linarith) hz)
  have huc := tendstoUniformlyOn_prod_of_tendsto hCc hDc hKs
    (fun q hq => hconv q ⟨intrinsicInterior_subset hq.1, intrinsicInterior_subset hq.2⟩)
    (isCompact_closedBall u (r / 2)) (hSC.trans hriC)
    (isCompact_closedBall v (r' / 2)) (hTD.trans hriD)
  have hcont : ContinuousWithinAt K
      (Metric.closedBall u (r / 2) ×ˢ Metric.closedBall v (r' / 2)) (u, v) := by
    have hnhd : ri C ×ˢ ri D ∈ 𝓝 ((u, v) : U × X) :=
      Filter.mem_of_superset ((hCo.prod hDo).mem_nhds ⟨hu, hv⟩) (Set.prod_mono hriC hriD)
    exact (((hK.continuousOn hCc hDc).continuousAt hnhd)).continuousWithinAt
  have hnw : Tendsto (fun i => (us i, vs i)) atTop
      (𝓝[Metric.closedBall u (r / 2) ×ˢ Metric.closedBall v (r' / 2)] (u, v)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hus.prodMk_nhds hvs, ?_⟩
    have h1 : ∀ᶠ i in atTop, us i ∈ Metric.closedBall u (r / 2) :=
      hus.eventually_mem (Metric.closedBall_mem_nhds u (show (0 : ℝ) < r / 2 by linarith))
    have h2 : ∀ᶠ i in atTop, vs i ∈ Metric.closedBall v (r' / 2) :=
      hvs.eventually_mem (Metric.closedBall_mem_nhds v (show (0 : ℝ) < r' / 2 by linarith))
    filter_upwards [h1, h2] with i h₁ h₂
    exact ⟨h₁, h₂⟩
  exact huc.tendsto_comp hcont hnw

/-- **The directional derivatives in the *convex* variable are upper semicontinuous along the
convergence**,
`limsup_i K_i'(u_i, v_i; 0, v') ≤ K'(u, v; 0, v')`.

Spelled without junk values: every real `μ` above `K'(u, v; 0, v')` eventually bounds
`K_i'(u_i, v_i; 0, v')`. A single step `α > 0` realises a secant slope of `K (u, ·)` below `μ`;
continuous convergence carries that slope to `K i` at the moving points; and the directional
derivative is below every secant slope. -/
theorem eventually_dirDerivReal_snd_lt (hCo : IsOpen C) (hCc : Convex ℝ C) (hDo : IsOpen D)
    (hDc : Convex ℝ D) (hKs : ∀ i, ConcaveConvexOn C D (Ks i)) (hK : ConcaveConvexOn C D K)
    (hconv : ∀ q ∈ C ×ˢ D, Tendsto (fun i => Ks i q) atTop (𝓝 (K q)))
    (hu : u ∈ C) (hv : v ∈ D) (hus : Tendsto us atTop (𝓝 u)) (hvs : Tendsto vs atTop (𝓝 v))
    {v' : X} {μ : ℝ} (hμ : dirDerivReal (fun x => K (u, x)) v v' < μ) :
    ∀ᶠ i in atTop, dirDerivReal (fun x => Ks i (us i, x)) (vs i) v' < μ := by
  obtain ⟨α, hαlt, hαD, hα0⟩ : ∃ α : ℝ, (K (u, v + α • v') - K (u, v)) / α < μ ∧
      v + α • v' ∈ D ∧ 0 < α :=
    (((tendsto_slope_dirDerivReal_of_convexOn hDo (hK.convex_snd u hu) hv v').eventually_lt_const
      hμ).and ((eventually_nhdsGT_add_smul_mem hDo hv v').and self_mem_nhdsWithin)).exists.imp
      fun _ h => ⟨h.1, h.2.1, h.2.2⟩
  have hbase := tendsto_eval_prod_of_tendsto hCo hCc hDo hDc hKs hK hconv hu hv hus hvs
  have hstep := tendsto_eval_prod_of_tendsto hCo hCc hDo hDc hKs hK hconv hu hαD hus
    (hvs.add tendsto_const_nhds)
  have hquot := ((hstep.sub hbase).div_const α).eventually_lt_const hαlt
  filter_upwards [hquot, hus.eventually_mem (hCo.mem_nhds hu),
    hvs.eventually_mem (hDo.mem_nhds hv),
    (hvs.add (tendsto_const_nhds (x := α • v'))).eventually_mem (hDo.mem_nhds hαD)]
    with i hqi hui hvi hvαi
  exact lt_of_le_of_lt
    (dirDerivReal_le_slope hDo ((hKs i).convex_snd (us i) hui) hvi hα0 hvαi) hqi

/-- **The directional derivatives in the *concave* variable are lower semicontinuous along the
convergence**,
`liminf_i K_i'(u_i, v_i; u', 0) ≥ K'(u, v; u', 0)`.

This is `eventually_dirDerivReal_snd_lt` read at `swapReal`, with the two sequences exchanged. -/
theorem eventually_lt_dirDerivReal_fst (hCo : IsOpen C) (hCc : Convex ℝ C) (hDo : IsOpen D)
    (hDc : Convex ℝ D) (hKs : ∀ i, ConcaveConvexOn C D (Ks i)) (hK : ConcaveConvexOn C D K)
    (hconv : ∀ q ∈ C ×ˢ D, Tendsto (fun i => Ks i q) atTop (𝓝 (K q)))
    (hu : u ∈ C) (hv : v ∈ D) (hus : Tendsto us atTop (𝓝 u)) (hvs : Tendsto vs atTop (𝓝 v))
    {u' : U} {μ : ℝ} (hμ : μ < dirDerivReal (fun w => K (w, v)) u u') :
    ∀ᶠ i in atTop, μ < dirDerivReal (fun w => Ks i (w, vs i)) (us i) u' := by
  have hconv' : ∀ q ∈ D ×ˢ C, Tendsto (fun i => swapReal (Ks i) q) atTop (𝓝 (swapReal K q)) :=
    fun q hq => by simpa only [swapReal_apply] using (hconv (q.2, q.1) ⟨hq.2, hq.1⟩).neg
  have hneg : dirDerivReal (fun w => swapReal K (v, w)) u u' < -μ := by
    have h := dirDerivReal_neg_of_tendsto (f := fun w => K (w, v))
      (tendsto_slope_dirDerivReal_of_concaveOn hCo (hK.concave_fst v hv) hu u')
    rw [← neg_lt_neg_iff, ← h] at hμ
    exact hμ
  filter_upwards [eventually_dirDerivReal_snd_lt hDo hDc hCo hCc (fun i => (hKs i).swapReal)
      hK.swapReal hconv' hv hu hvs hus hneg,
    hus.eventually_mem (hCo.mem_nhds hu), hvs.eventually_mem (hDo.mem_nhds hv)] with i hi hui hvi
  change dirDerivReal (-fun w => Ks i (w, vs i)) (us i) u' < -μ at hi
  rw [dirDerivReal_neg_of_tendsto (f := fun w => Ks i (w, vs i))
    (tendsto_slope_dirDerivReal_of_concaveOn hCo ((hKs i).concave_fst (vs i) hvi) hui u')] at hi
  exact neg_lt_neg_iff.1 hi

end Convergence

/-! ### Upper semicontinuity of the subdifferentials -/

section SubdifferentialConvergence

variable {U X : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  {C : Set U} {D : Set X} {Ks : ℕ → U × X → ℝ} {K : U × X → ℝ} {u : U} {v : X}
  {us : ℕ → U} {vs : ℕ → X}

omit [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] [NormedAddCommGroup X]
  [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] in
/-- Negating a set thickened by a ball thickens the negated set by the same ball: the closed ball
about the origin is symmetric. -/
theorem neg_add_closedBall_zero (S : Set U) (ε : ℝ) :
    -(S + Metric.closedBall (0 : U) ε) = -S + Metric.closedBall (0 : U) ε := by
  rw [neg_add]
  congr 1
  ext x
  simp

omit [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] in
/-- A product of thickened sets is contained in the thickening of the product. -/
theorem prod_add_prod_subset {A A' : Set U} {B B' : Set X} :
    (A + A') ×ˢ (B + B') ⊆ A ×ˢ B + A' ×ˢ B' := by
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  rw [Set.mem_add] at hx hy
  obtain ⟨a, ha, a', ha', hxa⟩ := hx
  obtain ⟨b, hb, b', hb', hyb⟩ := hy
  refine Set.mem_add.2 ⟨(a, b), ⟨ha, hb⟩, (a', b'), ⟨ha', hb'⟩, ?_⟩
  simp [hxa, hyb]

/-- **In the convex variable: `∂₂K_i(u_i, v_i) ⊆ ∂₂K(u, v) + εB` eventually.**

Upper semicontinuity of the one-variable subdifferential, applied to the convex slices
`K_i (u_i, ·)` extended by `+∞` off `D`; the family converges pointwise on `D` to `K (u, ·)` by
continuous convergence. -/
theorem eventually_subdifferentialSndOn_subset (hCo : IsOpen C) (hCc : Convex ℝ C) (hDo : IsOpen D)
    (hDc : Convex ℝ D) (hKs : ∀ i, ConcaveConvexOn C D (Ks i)) (hK : ConcaveConvexOn C D K)
    (hconv : ∀ q ∈ C ×ˢ D, Tendsto (fun i => Ks i q) atTop (𝓝 (K q)))
    (hu : u ∈ C) (hv : v ∈ D) (hus : Tendsto us atTop (𝓝 u)) (hvs : Tendsto vs atTop (𝓝 v))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, subdifferentialSndOn D (Ks i) (us i, vs i)
      ⊆ subdifferentialSndOn D K (u, v) + Metric.closedBall (0 : X) ε := by
  classical
  set us' : ℕ → U := fun i => if us i ∈ C then us i else u with hus'def
  have hus'C : ∀ i, us' i ∈ C := by
    intro i
    simp only [hus'def]
    split_ifs with h
    · exact h
    · exact hu
  have hus'eq : ∀ᶠ i in atTop, us' i = us i := by
    filter_upwards [hus.eventually_mem (hCo.mem_nhds hu)] with i hi
    simp [hus'def, hi]
  have hus' : Tendsto us' atTop (𝓝 u) := hus.congr' (hus'eq.mono fun i h => h.symm)
  have hfc : ∀ i,
      ConvexFn (ConvexAnalysis.convexRestrict D fun x => ((Ks i (us' i, x) : ℝ) : EReal)) :=
    fun i => (convexOn_iff_convexFn D _).1 ((hKs i).convex_snd (us' i) (hus'C i))
  have hgc : ConvexFn (ConvexAnalysis.convexRestrict D fun x => ((K (u, x) : ℝ) : EReal)) :=
    (convexOn_iff_convexFn D _).1 (hK.convex_snd u hu)
  have hconvD : ∀ x ∈ D, Tendsto
      (fun i => ConvexAnalysis.convexRestrict D (fun x => ((Ks i (us' i, x) : ℝ) : EReal)) x) atTop
      (𝓝 (ConvexAnalysis.convexRestrict D (fun x => ((K (u, x) : ℝ) : EReal)) x)) := by
    intro x hx
    have h := tendsto_eval_prod_of_tendsto hCo hCc hDo hDc hKs hK hconv hu hx hus'
      (tendsto_const_nhds (x := x))
    simp only [convexRestrict_of_mem hx]
    exact EReal.tendsto_coe.2 h
  have hmain := eventually_subdifferential_subset_add_closedBall hDo hDc hfc
    (fun _ => properConvex_convexRestrict_coe ⟨v, hv⟩ _)
        (fun _ => (convexDom_convexRestrict_coe D _).ge) hgc
    (properConvex_convexRestrict_coe ⟨v, hv⟩ _) (convexDom_convexRestrict_coe D _).ge hconvD
        hv hvs hε
  filter_upwards [hmain, hus'eq, hvs.eventually_mem (hDo.mem_nhds hv)] with i hi hui hvi
  rw [subdifferentialSndOn_eq_subdifferential (D := D) (K := Ks i) (p := (us i, vs i)) hvi,
    subdifferentialSndOn_eq_subdifferential (D := D) (K := K) (p := (u, v)) hv, ← hui]
  exact hi

/-- **In the concave variable: `∂₁K_i(u_i, v_i) ⊆ ∂₁K(u, v) + εB` eventually.**

The convex-variable statement read at `swapReal`: `∂₁` is the negated `∂₂` of the swap, and
negation carries the `ε`-thickening across because the ball is symmetric. -/
theorem eventually_superdifferentialFstOn_subset (hCo : IsOpen C) (hCc : Convex ℝ C)
    (hDo : IsOpen D)
    (hDc : Convex ℝ D) (hKs : ∀ i, ConcaveConvexOn C D (Ks i)) (hK : ConcaveConvexOn C D K)
    (hconv : ∀ q ∈ C ×ˢ D, Tendsto (fun i => Ks i q) atTop (𝓝 (K q)))
    (hu : u ∈ C) (hv : v ∈ D) (hus : Tendsto us atTop (𝓝 u)) (hvs : Tendsto vs atTop (𝓝 v))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, superdifferentialFstOn C (Ks i) (us i, vs i)
      ⊆ superdifferentialFstOn C K (u, v) + Metric.closedBall (0 : U) ε := by
  have hconv' : ∀ q ∈ D ×ˢ C, Tendsto (fun i => swapReal (Ks i) q) atTop (𝓝 (swapReal K q)) :=
    fun q hq => by simpa only [swapReal_apply] using (hconv (q.2, q.1) ⟨hq.2, hq.1⟩).neg
  filter_upwards [eventually_subdifferentialSndOn_subset hDo hDc hCo hCc
    (fun i => (hKs i).swapReal) hK.swapReal hconv' hv hu hvs hus hε] with i hi
  rw [superdifferentialFstOn_eq_neg_subdifferentialSndOn_swapReal,
    superdifferentialFstOn_eq_neg_subdifferentialSndOn_swapReal, Prod.swap_prod_mk,
        Prod.swap_prod_mk,
    ← neg_add_closedBall_zero]
  exact Set.neg_subset_neg.2 hi

/-- **`∂K_i(u_i, v_i) ⊆ ∂K(u, v) + εB` eventually**, with `B` the unit ball of `U × X`.

The subdifferential of a saddle-function is the *product* of the two one-variable ones, and the
unit ball of a product is the product of the unit balls (`Metric.closedBall_prod_same`), so the
statement is the conjunction of the previous two. -/
theorem eventually_saddleSubdifferentialOn_subset (hCo : IsOpen C) (hCc : Convex ℝ C)
    (hDo : IsOpen D)
    (hDc : Convex ℝ D) (hKs : ∀ i, ConcaveConvexOn C D (Ks i)) (hK : ConcaveConvexOn C D K)
    (hconv : ∀ q ∈ C ×ˢ D, Tendsto (fun i => Ks i q) atTop (𝓝 (K q)))
    (hu : u ∈ C) (hv : v ∈ D) (hus : Tendsto us atTop (𝓝 u)) (hvs : Tendsto vs atTop (𝓝 v))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, saddleSubdifferentialOn C D (Ks i) (us i, vs i)
      ⊆ saddleSubdifferentialOn C D K (u, v) + Metric.closedBall (0 : U × X) ε := by
  filter_upwards [
    eventually_superdifferentialFstOn_subset hCo hCc hDo hDc hKs hK hconv hu hv hus hvs hε,
    eventually_subdifferentialSndOn_subset hCo hCc hDo hDc hKs hK hconv hu hv hus hvs hε]
    with i h₁ h₂
  refine (Set.prod_mono h₁ h₂).trans ?_
  have hball : Metric.closedBall (0 : U) ε ×ˢ Metric.closedBall (0 : X) ε
      = Metric.closedBall (0 : U × X) ε := by
    ext q
    simp [Set.mem_prod, Metric.mem_closedBall, Prod.norm_def]
  rw [← hball]
  exact prod_add_prod_subset

end SubdifferentialConvergence

/-! ### The constant sequence: semicontinuity on the rectangle -/

section LocalSemicontinuity

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  {C : Set U} {D : Set X} {K : U × X → ℝ} {u : U} {v : X}

/-- `K'(u, v; u', 0)` is lower semicontinuous in `(u, v)` on `C × D`.

The sequential statement for the constant sequence `K, K, K, …`, transported from sequences to the
neighbourhood filter (`𝓝 (u, v)` is countably generated). -/
theorem lowerSemicontinuousAt_dirDerivReal_fst (hCo : IsOpen C) (hCc : Convex ℝ C)
    (hDo : IsOpen D) (hDc : Convex ℝ D) (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D)
    (u' : U) :
    LowerSemicontinuousAt (fun p : U × X => dirDerivReal (fun w => K (w, p.2)) p.1 u') (u, v) := by
  intro c hc
  rw [Filter.eventually_iff_seq_eventually]
  intro ps hps
  rw [nhds_prod_eq] at hps
  exact eventually_lt_dirDerivReal_fst hCo hCc hDo hDc (fun _ => hK) hK
    (fun _ _ => tendsto_const_nhds) hu hv hps.fst hps.snd hc

/-- `K'(u, v; 0, v')` is upper semicontinuous in `(u, v)` on `C × D`. -/
theorem upperSemicontinuousAt_dirDerivReal_snd (hCo : IsOpen C) (hCc : Convex ℝ C)
    (hDo : IsOpen D) (hDc : Convex ℝ D) (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D)
    (v' : X) :
    UpperSemicontinuousAt (fun p : U × X => dirDerivReal (fun x => K (p.1, x)) p.2 v') (u, v) := by
  intro c hc
  rw [Filter.eventually_iff_seq_eventually]
  intro ps hps
  rw [nhds_prod_eq] at hps
  exact eventually_dirDerivReal_snd_lt hCo hCc hDo hDc (fun _ => hK) hK
    (fun _ _ => tendsto_const_nhds) hu hv hps.fst hps.snd hc

end LocalSemicontinuity

section LocalSubdifferential

variable {U X : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  {C : Set U} {D : Set X} {K : U × X → ℝ} {u : U} {v : X}

/-- `∂K` is upper semicontinuous on `C × D`: `∂K(x, y) ⊆ ∂K(u, v) + εB` for every `(x, y)` near
`(u, v)`. -/
theorem eventually_nhds_saddleSubdifferentialOn_subset (hCo : IsOpen C) (hCc : Convex ℝ C)
    (hDo : IsOpen D) (hDc : Convex ℝ D) (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p in 𝓝 ((u, v) : U × X), saddleSubdifferentialOn C D K p
      ⊆ saddleSubdifferentialOn C D K (u, v) + Metric.closedBall (0 : U × X) ε := by
  rw [Filter.eventually_iff_seq_eventually]
  intro ps hps
  rw [nhds_prod_eq] at hps
  exact eventually_saddleSubdifferentialOn_subset hCo hCc hDo hDc (fun _ => hK) hK
    (fun _ _ => tendsto_const_nhds) hu hv hps.fst hps.snd hε

end LocalSubdifferential

/-! ### Tangent inequalities at a point of differentiability -/

section Tangent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E} {f : E → ℝ} {x : E}
  {L M : E →L[ℝ] ℝ}

/-- Where a real-valued function is Fréchet differentiable, `dirDerivReal` is the value of the
derivative in the given direction. -/
theorem dirDerivReal_eq_of_hasFDerivAt (hd : HasFDerivAt f L x) (y : E) :
    dirDerivReal f x y = L y :=
  dirDerivReal_eq_of_tendsto (tendsto_slope_ray_of_hasFDerivAt hd y)

/-- **The gradient inequality**: a convex function on an open set lies above its tangent at a point
of differentiability.

The difference quotient is nondecreasing in the step, so its limit at `0` — the derivative — is
below its value at step `1`, which is `f z - f x`. -/
theorem le_add_of_hasFDerivAt_of_convexOn (hS : IsOpen S) (hf : ConvexOn ℝ S f) (hx : x ∈ S)
    (hd : HasFDerivAt f L x) {z : E} (hz : z ∈ S) : f x + L (z - x) ≤ f z := by
  have hzx : x + (1 : ℝ) • (z - x) = z := by module
  have h := dirDerivReal_le_slope (y := z - x) hS hf hx one_pos (by rw [hzx]; exact hz)
  rw [dirDerivReal_eq_of_hasFDerivAt hd, hzx, div_one] at h
  linarith

/-- The gradient inequality for a concave function: it lies below its tangent. This is the convex
inequality for `-f`. -/
theorem le_add_of_hasFDerivAt_of_concaveOn (hS : IsOpen S) (hf : ConcaveOn ℝ S f) (hx : x ∈ S)
    (hd : HasFDerivAt f L x) {z : E} (hz : z ∈ S) : f z ≤ f x + L (z - x) := by
  have h := le_add_of_hasFDerivAt_of_convexOn hS hf.neg hx hd.neg hz
  have e : (-L) (z - x) = -L (z - x) := rfl
  simp only [Pi.neg_apply] at h
  linarith

/-- **A linear function that minorises the increment of `f` is the derivative.** No convexity is
used — only the limit of the difference quotient along the two opposite rays. -/
theorem eq_of_forall_add_le_of_hasFDerivAt (hS : IsOpen S) (hx : x ∈ S) (hd : HasFDerivAt f L x)
    (hM : ∀ z ∈ S, f x + M (z - x) ≤ f z) : M = L := by
  have hle : ∀ w : E, M w ≤ L w := by
    intro w
    refine ge_of_tendsto (tendsto_slope_ray_of_hasFDerivAt hd w) ?_
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsGT_add_smul_mem hS hx w] with t ht htS
    have h := hM _ htS
    rw [add_sub_cancel_left, map_smul, smul_eq_mul] at h
    rw [le_div_iff₀ (show (0 : ℝ) < t from ht)]
    linarith
  refine ContinuousLinearMap.ext fun w => le_antisymm (hle w) ?_
  have hneg := hle (-w)
  rw [map_neg, map_neg] at hneg
  linarith

/-- The same for a concave function: a linear majorant of the increment is the derivative. This is
the minorant statement for `-f`. -/
theorem eq_of_forall_le_add_of_hasFDerivAt (hS : IsOpen S) (hx : x ∈ S) (hd : HasFDerivAt f L x)
    (hM : ∀ z ∈ S, f z ≤ f x + M (z - x)) : M = L :=
  neg_injective <| eq_of_forall_add_le_of_hasFDerivAt hS hx hd.neg fun z hz => by
    have e : (-M) (z - x) = -M (z - x) := rfl
    simp only [Pi.neg_apply]
    linarith [hM z hz]

end Tangent

/-! ### The gradient of a saddle-function, as a pair -/

section GradientPair

variable {U X : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] {K : U × X → ℝ} {q p : U × X} {u : U} {v : X}

/-- The continuous linear functional on `U × X` represented by a pair `q = (u*, v*)`, namely
`(w, x) ↦ ⟪w, u*⟫ + ⟪x, v*⟫`.

A product of inner-product spaces carries the *supremum* norm in Mathlib, so `U × X` is not itself
an inner-product space and Mathlib's `gradient` does not apply to a function of a pair.
Rockafellar's `∇K (u, v)` is the pair `q` for which `prodInnerL q` is the Fréchet derivative. -/
noncomputable def prodInnerL (q : U × X) : (U × X) →L[ℝ] ℝ :=
  (innerSL ℝ q.1).comp (ContinuousLinearMap.fst ℝ U X) +
    (innerSL ℝ q.2).comp (ContinuousLinearMap.snd ℝ U X)

@[simp] theorem prodInnerL_apply (q p : U × X) : prodInnerL q p = ⟪p.1, q.1⟫ + ⟪p.2, q.2⟫ := by
  have h : prodInnerL q p = ⟪q.1, p.1⟫ + ⟪q.2, p.2⟫ := rfl
  rw [h, real_inner_comm q.1 p.1, real_inner_comm q.2 p.2]

/-- `∇K p = q`: `K` is Fréchet differentiable at `p` with derivative `prodInnerL q`. This is
Rockafellar's gradient of a finite saddle-function, split into its two blocks. -/
def HasSaddleGradientAt (K : U × X → ℝ) (q p : U × X) : Prop :=
  HasFDerivAt K (prodInnerL q) p

/-- A saddle-function with a gradient is differentiable. -/
theorem HasSaddleGradientAt.differentiableAt (h : HasSaddleGradientAt K q p) :
    DifferentiableAt ℝ K p :=
  HasFDerivAt.differentiableAt h

/-- The concave slice of a differentiable saddle-function is differentiable, with the first block
of the gradient as its derivative. -/
theorem HasSaddleGradientAt.hasFDerivAt_fst (h : HasSaddleGradientAt K q (u, v)) :
    HasFDerivAt (fun w => K (w, v)) (innerSL ℝ q.1) u := by
  have hL : (prodInnerL q).comp (ContinuousLinearMap.inl ℝ U X) = innerSL ℝ q.1 :=
    ContinuousLinearMap.ext fun w => by simp [real_inner_comm]
  rw [← hL]
  exact HasFDerivAt.comp (f := fun w : U => (w, v)) u h (hasFDerivAt_prodMk_left u v)

/-- The convex slice of a differentiable saddle-function is differentiable, with the second block
of the gradient as its derivative. -/
theorem HasSaddleGradientAt.hasFDerivAt_snd (h : HasSaddleGradientAt K q (u, v)) :
    HasFDerivAt (fun x => K (u, x)) (innerSL ℝ q.2) v := by
  have hL : (prodInnerL q).comp (ContinuousLinearMap.inr ℝ U X) = innerSL ℝ q.2 :=
    ContinuousLinearMap.ext fun w => by simp [real_inner_comm]
  rw [← hL]
  exact HasFDerivAt.comp (f := fun x : X => (u, x)) v h (hasFDerivAt_prodMk_right u v)

/-- In finite dimensions every continuous linear functional on `U × X` is a `prodInnerL`, by the
Riesz representation in each factor. -/
theorem exists_prodInnerL_eq [FiniteDimensional ℝ U] [FiniteDimensional ℝ X]
    (L : (U × X) →L[ℝ] ℝ) : ∃ q : U × X, prodInnerL q = L := by
  obtain ⟨a, ha⟩ := (InnerProductSpace.toDual ℝ U).surjective
    (L.comp (ContinuousLinearMap.inl ℝ U X))
  obtain ⟨b, hb⟩ := (InnerProductSpace.toDual ℝ X).surjective
    (L.comp (ContinuousLinearMap.inr ℝ U X))
  have ha' : ∀ w : U, ⟪a, w⟫ = L (w, 0) := fun w => by simpa using DFunLike.congr_fun ha w
  have hb' : ∀ z : X, ⟪b, z⟫ = L (0, z) := fun z => by simpa using DFunLike.congr_fun hb z
  refine ⟨(a, b), ContinuousLinearMap.ext fun z => ?_⟩
  have hsplit : ((z.1, 0) : U × X) + ((0, z.2) : U × X) = z := by
    rw [Prod.mk_add_mk, add_zero, zero_add]
  have hval : prodInnerL (a, b) z = L (z.1, 0) + L (0, z.2) := by
    change ⟪a, z.1⟫ + ⟪b, z.2⟫ = _
    rw [ha' z.1, hb' z.2]
  rw [hval, ← map_add, hsplit]

/-- In finite dimensions, being differentiable and having a saddle-gradient are the same. -/
theorem differentiableAt_iff_exists_hasSaddleGradientAt [FiniteDimensional ℝ U]
    [FiniteDimensional ℝ X] (K : U × X → ℝ) (p : U × X) :
    DifferentiableAt ℝ K p ↔ ∃ q, HasSaddleGradientAt K q p := by
  refine ⟨fun h => ?_, fun hq => HasSaddleGradientAt.differentiableAt hq.choose_spec⟩
  obtain ⟨q, hq⟩ := exists_prodInnerL_eq (fderiv ℝ K p)
  exact ⟨q, show HasFDerivAt K (prodInnerL q) p by rw [hq]; exact h.hasFDerivAt⟩

end GradientPair

/-! ### Thickening a singleton -/

section Thicken

variable {E : Type*} [NormedAddCommGroup E]

/-- Membership in a singleton thickened by a closed ball about the origin is a bound on the
distance to that point. -/
theorem norm_sub_le_of_mem_singleton_add_closedBall {a b : E} {ε : ℝ}
    (h : b ∈ ({a} : Set E) + Metric.closedBall (0 : E) ε) : ‖b - a‖ ≤ ε := by
  obtain ⟨z, hz, w, hw, hzw⟩ := Set.mem_add.1 h
  rw [Set.mem_singleton_iff] at hz
  rw [← hzw, hz]
  simpa using hw

end Thicken


/-! ### Differentiability and a unique subgradient -/

section SaddleGradient

variable {U X : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  {C : Set U} {D : Set X} {K : U × X → ℝ} {u : U} {v : X} {p q : U × X}

/-- The subdifferential of a saddle-function is a singleton exactly when each of its two blocks is,
provided both are nonempty. It is a product, so this is not automatic: an empty factor makes the
product empty whatever the other factor is. -/
theorem saddleSubdifferentialOn_eq_singleton_iff (hne₁ : (superdifferentialFstOn C K p).Nonempty)
    (hne₂ : (subdifferentialSndOn D K p).Nonempty) :
    saddleSubdifferentialOn C D K p = {q} ↔
      superdifferentialFstOn C K p = {q.1} ∧ subdifferentialSndOn D K p = {q.2} := by
  have hprod : saddleSubdifferentialOn C D K p
      = superdifferentialFstOn C K p ×ˢ subdifferentialSndOn D K p := rfl
  constructor
  · intro h
    obtain ⟨a, ha⟩ := hne₁
    obtain ⟨b, hb⟩ := hne₂
    have hq : q ∈ saddleSubdifferentialOn C D K p := by rw [h]; exact Set.mem_singleton_iff.2 rfl
    refine ⟨Set.eq_singleton_iff_unique_mem.2 ⟨hq.1, fun y hy => ?_⟩,
      Set.eq_singleton_iff_unique_mem.2 ⟨hq.2, fun y hy => ?_⟩⟩
    · have hmem : ((y, b) : U × X) ∈ saddleSubdifferentialOn C D K p := ⟨hy, hb⟩
      rw [h, Set.mem_singleton_iff] at hmem
      exact congrArg Prod.fst hmem
    · have hmem : ((a, y) : U × X) ∈ saddleSubdifferentialOn C D K p := ⟨ha, hy⟩
      rw [h, Set.mem_singleton_iff] at hmem
      exact congrArg Prod.snd hmem
  · rintro ⟨h₁, h₂⟩
    rw [hprod, h₁, h₂, Set.singleton_prod_singleton]

/-- At a point where `K` is differentiable the first block of `∇K` is the only element of
`∂₁K(u, v)`. -/
theorem superdifferentialFstOn_eq_singleton_of_hasSaddleGradientAt (hCo : IsOpen C)
    (hK : ConcaveOn ℝ C fun w => K (w, v)) (hu : u ∈ C)
    (hd : HasSaddleGradientAt K q (u, v)) : superdifferentialFstOn C K (u, v) = {q.1} := by
  have hs := HasSaddleGradientAt.hasFDerivAt_fst hd
  refine Set.eq_singleton_iff_unique_mem.2 ⟨?_, fun y hy => ?_⟩
  · simp only [mem_superdifferentialFstOn]
    intro w hw
    have h := le_add_of_hasFDerivAt_of_concaveOn hCo hK hu hs hw
    rwa [innerSL_apply_apply, real_inner_comm] at h
  · simp only [mem_superdifferentialFstOn] at hy
    refine innerSL_inj.1 (eq_of_forall_le_add_of_hasFDerivAt hCo hu hs fun z hz => ?_)
    rw [innerSL_apply_apply, real_inner_comm]
    exact hy z hz

/-- The same in the convex variable: the second block of `∇K` is the only element of
`∂₂K(u, v)`. -/
theorem subdifferentialSndOn_eq_singleton_of_hasSaddleGradientAt (hDo : IsOpen D)
    (hK : ConvexOn ℝ D fun x => K (u, x)) (hv : v ∈ D)
    (hd : HasSaddleGradientAt K q (u, v)) : subdifferentialSndOn D K (u, v) = {q.2} := by
  have hs := HasSaddleGradientAt.hasFDerivAt_snd hd
  refine Set.eq_singleton_iff_unique_mem.2 ⟨?_, fun y hy => ?_⟩
  · simp only [mem_subdifferentialSndOn]
    intro x hx
    have h := le_add_of_hasFDerivAt_of_convexOn hDo hK hv hs hx
    rwa [innerSL_apply_apply, real_inner_comm] at h
  · simp only [mem_subdifferentialSndOn] at hy
    refine innerSL_inj.1 (eq_of_forall_add_le_of_hasFDerivAt hDo hv hs fun z hz => ?_)
    rw [innerSL_apply_apply, real_inner_comm]
    exact hy z hz

/-- Where a finite concave-convex function is differentiable, its gradient is its unique
subgradient. -/
theorem saddleSubdifferentialOn_eq_singleton_of_hasSaddleGradientAt (hCo : IsOpen C)
    (hDo : IsOpen D)
    (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D)
    (hd : HasSaddleGradientAt K q (u, v)) : saddleSubdifferentialOn C D K (u, v) = {q} := by
  have hprod : saddleSubdifferentialOn C D K (u, v)
      = superdifferentialFstOn C K (u, v) ×ˢ subdifferentialSndOn D K (u, v) := rfl
  rw [hprod,
      superdifferentialFstOn_eq_singleton_of_hasSaddleGradientAt hCo (hK.concave_fst v hv) hu hd,
    subdifferentialSndOn_eq_singleton_of_hasSaddleGradientAt hDo (hK.convex_snd u hu) hv hd,
    Set.singleton_prod_singleton]

end SaddleGradient

section Differentiable

variable {U X : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  {C : Set U} {D : Set X} {K : U × X → ℝ} {u : U} {v : X} {q : U × X}

omit [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] in
/-- `∂₂K(u, v)` is nonempty at every point of the open rectangle: a convex function has a
subgradient wherever it is finite on a neighbourhood. -/
theorem subdifferentialSndOn_nonempty (hDo : IsOpen D) (hDc : Convex ℝ D)
    (hK : ConvexOn ℝ D fun x => K (u, x)) (hv : v ∈ D) :
    (subdifferentialSndOn D K (u, v)).Nonempty := by
  have hf : ConvexFn (ConvexAnalysis.convexRestrict D fun x => ((K (u, x) : ℝ) : EReal)) :=
    (convexOn_iff_convexFn D _).1 hK
  have hri : v
      ∈ ri (convexDom (ConvexAnalysis.convexRestrict D fun x => ((K (u, x) : ℝ) : EReal))) := by
    rw [convexDom_convexRestrict_coe]
    exact Convex.interior_subset_relint hDc ⟨v, by rwa [hDo.interior_eq]⟩
      (by rwa [hDo.interior_eq])
  rw [subdifferentialSndOn_eq_subdifferential (D := D) (K := K) (p := (u, v)) hv]
  exact subdifferential_nonempty_of_mem_relint_convexDom
      hf (properConvex_convexRestrict_coe ⟨v, hv⟩ _) hri

omit [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] in
/-- `∂₁K(u, v)` is nonempty at every point of the open rectangle: the convex statement read at
`swapReal`. -/
theorem superdifferentialFstOn_nonempty (hCo : IsOpen C) (hCc : Convex ℝ C)
    (hK : ConcaveOn ℝ C fun w => K (w, v)) (hu : u ∈ C) :
    (superdifferentialFstOn C K (u, v)).Nonempty := by
  rw [superdifferentialFstOn_eq_neg_subdifferentialSndOn_swapReal, Prod.swap_prod_mk,
      Set.nonempty_neg]
  exact subdifferentialSndOn_nonempty (K := swapReal K) hCo hCc hK.neg hu

/-- Upper semicontinuity of `∂₁K` on the rectangle, in the concave variable alone. -/
theorem eventually_nhds_superdifferentialFstOn_subset (hCo : IsOpen C) (hCc : Convex ℝ C)
    (hDo : IsOpen D) (hDc : Convex ℝ D) (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z in 𝓝 ((u, v) : U × X), superdifferentialFstOn C K z
      ⊆ superdifferentialFstOn C K (u, v) + Metric.closedBall (0 : U) ε := by
  rw [Filter.eventually_iff_seq_eventually]
  intro ps hps
  rw [nhds_prod_eq] at hps
  exact eventually_superdifferentialFstOn_subset hCo hCc hDo hDc (fun _ => hK) hK
    (fun _ _ => tendsto_const_nhds) hu hv hps.fst hps.snd hε

/-- Upper semicontinuity of `∂₂K` on the rectangle, in the convex variable alone. -/
theorem eventually_nhds_subdifferentialSndOn_subset (hCo : IsOpen C) (hCc : Convex ℝ C)
    (hDo : IsOpen D) (hDc : Convex ℝ D) (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z in 𝓝 ((u, v) : U × X), subdifferentialSndOn D K z
      ⊆ subdifferentialSndOn D K (u, v) + Metric.closedBall (0 : X) ε := by
  rw [Filter.eventually_iff_seq_eventually]
  intro ps hps
  rw [nhds_prod_eq] at hps
  exact eventually_subdifferentialSndOn_subset hCo hCc hDo hDc (fun _ => hK) hK
    (fun _ _ => tendsto_const_nhds) hu hv hps.fst hps.snd hε

/-- **Converse half**: a finite concave-convex function with a *unique* subgradient at a point of
an open rectangle is differentiable there, jointly in the two variables.

The proof is not the book's, which upgrades separate to joint differentiability through uniform
convergence of the rescalings
`h_λ (x, y) = [K (u + λx, v + λy) - K (u, v) - λ⟪x, u*⟫ - λ⟪y, v*⟫] / λ`. Upper semicontinuity of
`∂K` gives the estimate outright: the increment `K (u + a, v + b) - K (u, v)` is sandwiched by
subgradient inequalities at `(u, v)`, `(u, v + b)` and `(u + a, v + b)`, each of whose subgradients
lies within `ε` of `q`, so the error is at most `ε (‖a‖ + ‖b‖)`. -/
theorem hasSaddleGradientAt_of_subdifferential_eq_singleton (hCo : IsOpen C) (hCc : Convex ℝ C)
    (hDo : IsOpen D) (hDc : Convex ℝ D) (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D)
    (h₁ : superdifferentialFstOn C K (u, v) = {q.1})
        (h₂ : subdifferentialSndOn D K (u, v) = {q.2}) :
    HasSaddleGradientAt K q (u, v) := by
  change HasFDerivAt K (prodInnerL q) ((u, v) : U × X)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  have hε : (0 : ℝ) < c / 2 := by linarith
  have hq1 : q.1 ∈ superdifferentialFstOn C K (u, v) :=
      by rw [h₁]; exact Set.mem_singleton_iff.2 rfl
  have hq2 : q.2 ∈ subdifferentialSndOn D K (u, v) := by rw [h₂]; exact Set.mem_singleton_iff.2 rfl
  simp only [mem_superdifferentialFstOn] at hq1
  simp only [mem_subdifferentialSndOn] at hq2
  have hCmem : ∀ᶠ z : U × X in 𝓝 ((u, v) : U × X), z.1 ∈ C :=
    (hCo.preimage continuous_fst).mem_nhds hu
  have hDmem : ∀ᶠ z : U × X in 𝓝 ((u, v) : U × X), z.2 ∈ D :=
    (hDo.preimage continuous_snd).mem_nhds hv
  have hFsub := eventually_nhds_superdifferentialFstOn_subset hCo hCc hDo hDc hK hu hv hε
  have hSsub := eventually_nhds_subdifferentialSndOn_subset hCo hCc hDo hDc hK hu hv hε
  have hmove : Tendsto (fun h : U × X => ((u + h.1, v + h.2) : U × X)) (𝓝 0) (𝓝 (u, v)) := by
    have hcont : Continuous fun h : U × X => ((u + h.1, v + h.2) : U × X) := by fun_prop
    simpa using hcont.tendsto 0
  have hmid : Tendsto (fun h : U × X => ((u, v + h.2) : U × X)) (𝓝 0) (𝓝 (u, v)) := by
    have hcont : Continuous fun h : U × X => ((u, v + h.2) : U × X) := by fun_prop
    simpa using hcont.tendsto 0
  filter_upwards [hmove.eventually hCmem, hmove.eventually hDmem, hmove.eventually hFsub,
    hmid.eventually hFsub, hmid.eventually hSsub] with h hxC hyD hFp hFm hSm
  obtain ⟨b, hb⟩ := subdifferentialSndOn_nonempty (u := u) (v := v + h.2) hDo hDc
    (hK.convex_snd u hu) hyD
  obtain ⟨a, ha⟩ := superdifferentialFstOn_nonempty (u := u) (v := v + h.2) hCo hCc
    (hK.concave_fst (v + h.2) hyD) hu
  obtain ⟨a', ha'⟩ := superdifferentialFstOn_nonempty (u := u + h.1) (v := v + h.2) hCo hCc
    (hK.concave_fst (v + h.2) hyD) hxC
  have hbε : ‖b - q.2‖ ≤ c / 2 := by
    refine norm_sub_le_of_mem_singleton_add_closedBall ?_
    have hmem := hSm hb
    rwa [h₂] at hmem
  have haε : ‖a - q.1‖ ≤ c / 2 := by
    refine norm_sub_le_of_mem_singleton_add_closedBall ?_
    have hmem := hFm ha
    rwa [h₁] at hmem
  have ha'ε : ‖a' - q.1‖ ≤ c / 2 := by
    refine norm_sub_le_of_mem_singleton_add_closedBall ?_
    have hmem := hFp ha'
    rwa [h₁] at hmem
  simp only [mem_subdifferentialSndOn] at hb
  simp only [mem_superdifferentialFstOn] at ha ha'
  have e1 : v + h.2 - v = h.2 := by abel
  have e2 : v - (v + h.2) = -h.2 := by abel
  have e3 : u + h.1 - u = h.1 := by abel
  have e4 : u - (u + h.1) = -h.1 := by abel
  have hA1 := hq2 (v + h.2) hyD
  have hA2 := hb v hv
  have hB1 := ha (u + h.1) hxC
  have hB2 := ha' u hu
  rw [e1] at hA1
  rw [e2, inner_neg_left] at hA2
  rw [e3] at hB1
  rw [e4, inner_neg_left] at hB2
  have hcsb : ⟪h.2, b⟫ - ⟪h.2, q.2⟫ ≤ ‖h.2‖ * (c / 2) := by
    have hsplit : ⟪h.2, b - q.2⟫ = ⟪h.2, b⟫ - ⟪h.2, q.2⟫ := inner_sub_right ..
    rw [← hsplit]
    exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hbε (norm_nonneg _))
  have hcsa : ⟪h.1, a⟫ - ⟪h.1, q.1⟫ ≤ ‖h.1‖ * (c / 2) := by
    have hsplit : ⟪h.1, a - q.1⟫ = ⟪h.1, a⟫ - ⟪h.1, q.1⟫ := inner_sub_right ..
    rw [← hsplit]
    exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left haε (norm_nonneg _))
  have hcsa' : ⟪h.1, q.1⟫ - ⟪h.1, a'⟫ ≤ ‖h.1‖ * (c / 2) := by
    have hsplit : ⟪h.1, q.1 - a'⟫ = ⟪h.1, q.1⟫ - ⟪h.1, a'⟫ := inner_sub_right ..
    have hnorm : ‖q.1 - a'‖ ≤ c / 2 := by rwa [norm_sub_rev]
    rw [← hsplit]
    exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _))
  have hn1 : ‖h.1‖ ≤ ‖h‖ := norm_fst_le h
  have hn2 : ‖h.2‖ ≤ ‖h‖ := norm_snd_le h
  have hnn1 : 0 ≤ ‖h.1‖ * (c / 2) := by positivity
  have hnn2 : 0 ≤ ‖h.2‖ * (c / 2) := by positivity
  have hbound : ‖h.1‖ * (c / 2) + ‖h.2‖ * (c / 2) ≤ c * ‖h‖ := by nlinarith
  have hpt : ((u, v) : U × X) + h = (u + h.1, v + h.2) := rfl
  rw [hpt, prodInnerL_apply, Real.norm_eq_abs, abs_le]
  exact ⟨by linarith, by linarith⟩

/-- A finite concave-convex function is differentiable at a point of an open rectangle exactly when
it has a unique subgradient there, and the gradient is then that subgradient. -/
theorem hasSaddleGradientAt_iff_saddleSubdifferentialOn_eq_singleton (hCo : IsOpen C)
    (hCc : Convex ℝ C) (hDo : IsOpen D) (hDc : Convex ℝ D) (hK : ConcaveConvexOn C D K) (hu : u ∈ C)
    (hv : v ∈ D) :
    HasSaddleGradientAt K q (u, v) ↔ saddleSubdifferentialOn C D K (u, v) = {q} := by
  refine ⟨saddleSubdifferentialOn_eq_singleton_of_hasSaddleGradientAt hCo hDo hK hu hv, fun h => ?_⟩
  obtain ⟨h₁, h₂⟩ := (saddleSubdifferentialOn_eq_singleton_iff
    (superdifferentialFstOn_nonempty hCo hCc (hK.concave_fst v hv) hu)
    (subdifferentialSndOn_nonempty hDo hDc (hK.convex_snd u hu) hv)).1 h
  exact hasSaddleGradientAt_of_subdifferential_eq_singleton hCo hCc hDo hDc hK hu hv h₁ h₂

/-- The same without naming the gradient: differentiability and unique subdifferentiability are the
same property. -/
theorem differentiableAt_iff_exists_saddleSubdifferentialOn_eq_singleton (hCo : IsOpen C)
    (hCc : Convex ℝ C) (hDo : IsOpen D) (hDc : Convex ℝ D) (hK : ConcaveConvexOn C D K)
    (hu : u ∈ C) (hv : v ∈ D) :
    DifferentiableAt ℝ K (u, v) ↔ ∃ q, saddleSubdifferentialOn C D K (u, v) = {q} := by
  rw [differentiableAt_iff_exists_hasSaddleGradientAt]
  exact exists_congr fun q =>
    hasSaddleGradientAt_iff_saddleSubdifferentialOn_eq_singleton hCo hCc hDo hDc hK hu hv

end Differentiable

/-! ### Subgradients through the directional derivative, in real form -/

section DirDerivSubdifferential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {S : Set E} {f : E → ℝ}
  {x y z : E}

/-- An inner product separates points on the right, and a one-sided comparison is enough because
directions come in pairs. -/
theorem eq_of_forall_real_inner_le (h : ∀ w : E, ⟪w, y⟫ ≤ ⟪w, z⟫) : y = z := by
  have hall : ∀ w : E, ⟪w, y⟫ = ⟪w, z⟫ := by
    intro w
    refine le_antisymm (h w) ?_
    have hneg := h (-w)
    rw [inner_neg_left, inner_neg_left] at hneg
    linarith
  have hzero : ⟪y - z, y - z⟫ = (0 : ℝ) := by
    rw [inner_sub_right, hall (y - z), sub_self]
  exact sub_eq_zero.1 (inner_self_eq_zero.1 hzero)

/-- `y` satisfies the subgradient inequality of `f` at `x` on `S` exactly when `⟪w, y⟫ ≤ f'(x; w)`
in every direction `w`.

Rockafellar states it as "`cl f'(x; ·)` is the support function of `∂f(x)`"; at an interior point
of an open set no closure is needed, and this is the pointwise reading. -/
theorem forall_inner_le_dirDerivReal_iff (hS : IsOpen S) (hf : ConvexOn ℝ S f) (hx : x ∈ S) :
    (∀ w : E, ⟪w, y⟫ ≤ dirDerivReal f x w) ↔ ∀ z ∈ S, f x + ⟪z - x, y⟫ ≤ f z := by
  constructor
  · intro h z hz
    have hzx : x + (1 : ℝ) • (z - x) = z := by module
    have hle := dirDerivReal_le_slope (y := z - x) hS hf hx one_pos (by rw [hzx]; exact hz)
    rw [hzx, div_one] at hle
    linarith [h (z - x)]
  · intro h w
    refine ge_of_tendsto (tendsto_slope_dirDerivReal_of_convexOn hS hf hx w) ?_
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsGT_add_smul_mem hS hx w] with t ht htS
    have hsub := h _ htS
    rw [add_sub_cancel_left, real_inner_smul_left] at hsub
    rw [le_div_iff₀ (show (0 : ℝ) < t from ht)]
    linarith

/-- The concave case: `y` is a supergradient exactly when `f'(x; w) ≤ ⟪w, y⟫` in every direction.
This is the convex statement for `-f` and `-y`. -/
theorem forall_dirDerivReal_le_inner_iff (hS : IsOpen S) (hf : ConcaveOn ℝ S f) (hx : x ∈ S) :
    (∀ w : E, dirDerivReal f x w ≤ ⟪w, y⟫) ↔ ∀ z ∈ S, f z ≤ f x + ⟪z - x, y⟫ := by
  refine (forall_congr' fun w => ?_).trans
    ((forall_inner_le_dirDerivReal_iff (y := -y) hS hf.neg hx).trans
      (forall₂_congr fun z _ => ?_))
  · rw [dirDerivReal_neg_of_tendsto (tendsto_slope_dirDerivReal_of_concaveOn hS hf hx w),
      inner_neg_right, neg_le_neg_iff]
  · rw [inner_neg_right, Pi.neg_apply, Pi.neg_apply]
    constructor <;> intro h <;> linarith

end DirDerivSubdifferential

/-! ### Differentiability is linearity of `K'(u, v; ·, ·)` -/

section LinearDirDeriv

variable {U X : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  {C : Set U} {D : Set X} {K : U × X → ℝ} {u : U} {v : X} {q : U × X}

omit [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [FiniteDimensional ℝ X] in
/-- A partial directional derivative equal to the linear function `⟪·, q.2⟫` pins `∂₂K(u, v)` down
to `{q.2}`, for the convex variable. Unlike the usual Gâteaux criterion this needs no upgrade to
Fréchet differentiability, because its conclusion is about subgradients. -/
theorem subdifferentialSndOn_eq_singleton_of_dirDerivReal (hDo : IsOpen D)
    (hK : ConvexOn ℝ D fun x => K (u, x)) (hv : v ∈ D)
    (h : ∀ w : X, dirDerivReal (fun x => K (u, x)) v w = ⟪w, q.2⟫) :
    subdifferentialSndOn D K (u, v) = {q.2} := by
  refine Set.eq_singleton_iff_unique_mem.2 ⟨?_, fun y hy => ?_⟩
  · simp only [mem_subdifferentialSndOn]
    exact (forall_inner_le_dirDerivReal_iff hDo hK hv).1 fun w => (h w).ge
  · simp only [mem_subdifferentialSndOn] at hy
    have hy' := (forall_inner_le_dirDerivReal_iff hDo hK hv).2 hy
    exact eq_of_forall_real_inner_le fun w => (hy' w).trans (h w).le

omit [FiniteDimensional ℝ U] [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] in
/-- The same for the concave variable: `∂₁K(u, v)` is pinned down to `{q.1}`. This is the convex
statement read at `swapReal`. -/
theorem superdifferentialFstOn_eq_singleton_of_dirDerivReal (hCo : IsOpen C)
    (hK : ConcaveOn ℝ C fun w => K (w, v)) (hu : u ∈ C)
    (h : ∀ w : U, dirDerivReal (fun w => K (w, v)) u w = ⟪w, q.1⟫) :
    superdifferentialFstOn C K (u, v) = {q.1} := by
  have h' : ∀ w : U, dirDerivReal (fun x => swapReal K (v, x)) u w = ⟪w, (v, -q.1).2⟫ := by
    intro w
    change dirDerivReal (-fun x => K (x, v)) u w = _
    rw [dirDerivReal_neg_of_tendsto (f := fun w => K (w, v))
      (tendsto_slope_dirDerivReal_of_concaveOn hCo hK hu w), h w, inner_neg_right]
  rw [superdifferentialFstOn_eq_neg_subdifferentialSndOn_swapReal, Prod.swap_prod_mk,
    subdifferentialSndOn_eq_singleton_of_dirDerivReal hCo hK.neg hu h', Set.neg_singleton, neg_neg]

/-- `∇K(u, v) = q` exactly when `K'(u, v; ·, ·)` is the linear function `prodInnerL q`. The forward
direction needs no hypothesis; the converse restricts the identity to the two axes, turns each into
a one-point subdifferential, and invokes the differentiability criterion. -/
theorem hasSaddleGradientAt_iff_forall_dirDerivReal_eq (hCo : IsOpen C) (hCc : Convex ℝ C)
    (hDo : IsOpen D) (hDc : Convex ℝ D) (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D) :
    HasSaddleGradientAt K q (u, v) ↔ ∀ z : U × X, dirDerivReal K (u, v) z = prodInnerL q z := by
  refine ⟨fun hd z => dirDerivReal_eq_of_hasFDerivAt hd z, fun h => ?_⟩
  have hfst : ∀ w : U, dirDerivReal (fun w => K (w, v)) u w = ⟪w, q.1⟫ := by
    intro w
    rw [← dirDerivReal_prod_fst hCo hDo hK hu hv w, h (w, 0), prodInnerL_apply]
    simp
  have hsnd : ∀ w : X, dirDerivReal (fun x => K (u, x)) v w = ⟪w, q.2⟫ := by
    intro w
    rw [← dirDerivReal_prod_snd hCo hDo hK hu hv w, h (0, w), prodInnerL_apply]
    simp
  exact hasSaddleGradientAt_of_subdifferential_eq_singleton hCo hCc hDo hDc hK hu hv
    (superdifferentialFstOn_eq_singleton_of_dirDerivReal hCo (hK.concave_fst v hv) hu hfst)
    (subdifferentialSndOn_eq_singleton_of_dirDerivReal hDo (hK.convex_snd u hu) hv hsnd)

/-- For a concave-convex function already finite on an open rectangle — Rockafellar's "`K` is
finite on a neighbourhood of `(u, v)`" — differentiability at `(u, v)` is exactly linearity of
`K'(u, v; ·, ·)`.

The book's last clause, that finiteness of the `m + n` two-sided partial derivatives already
suffices, is not formalised: it is a statement about a coordinate basis rather than about the
space. -/
theorem differentiableAt_iff_isLinearMap_dirDerivReal (hCo : IsOpen C) (hCc : Convex ℝ C)
    (hDo : IsOpen D) (hDc : Convex ℝ D) (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D) :
    DifferentiableAt ℝ K (u, v) ↔ IsLinearMap ℝ (dirDerivReal K (u, v)) := by
  rw [differentiableAt_iff_exists_hasSaddleGradientAt]
  constructor
  · rintro ⟨r, hr⟩
    have heq : dirDerivReal K (u, v) = ⇑(prodInnerL r) :=
      funext fun z => dirDerivReal_eq_of_hasFDerivAt hr z
    rw [heq]
    exact (prodInnerL r).toLinearMap.isLinear
  · intro h
    obtain ⟨r, hr⟩ := exists_prodInnerL_eq (LinearMap.toContinuousLinearMap (IsLinearMap.mk' _ h))
    refine ⟨r, (hasSaddleGradientAt_iff_forall_dirDerivReal_eq hCo hCc hDo hDc hK hu hv).2
      fun z => ?_⟩
    rw [hr]
    simp

end LinearDirDeriv

end ConvexAnalysis
