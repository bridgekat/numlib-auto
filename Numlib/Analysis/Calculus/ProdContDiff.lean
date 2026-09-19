/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Calculus.ContDiff.Basic` for the class and the induction,
`Mathlib.Analysis.Calculus.FDeriv.Partial` for the differentiability from partial derivatives.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Numlib.Analysis.Calculus.ContDiffOnClosure

/-!
# Smoothness on a product `E × ℝ` from partial derivatives, up to the boundary

A function `f (x, t)` of a space variable `x ∈ Ω ⊆ E` (`Ω` open) and a time variable `t ∈ s ⊆ ℝ`
is `C^k` on `Ω ×ˢ s` as soon as its partial derivatives `∂ₜ^j D_x^i f`, `i + j ≤ k`, exist and
are jointly continuous. Mathlib has the differentiability of a function of two variables from
partial derivatives that are continuous *at a point of an open set*
(`hasStrictFDerivAt_uncurry_coprod`, `isLittleO_sub_sub_fderiv`); this module carries the
statement to a set `Ω ×ˢ s` that need not be open in the time direction (`s = [0, ∞)`, say), to
every order, and *with the derivatives extending continuously to a larger set* — the class
`C^k(Ω̄ × s)` in which the evolution equations of Brezis, *Functional Analysis, Sobolev Spaces
and Partial Differential Equations*, chapter 10, state their regularity.

## The class `ContDiffOnExtendsTo`

`ContDiffOnExtendsTo 𝕜 n f s t` says that `f` is `C^n` on `s` and that each iterated derivative
within `s`, `iteratedFDerivWithin 𝕜 m f s` for `m ≤ n`, agrees on `s` with a function continuous
on `t`. With `s` open and `t = closure s` it is `ContDiffOnClosure` (the class `C^n(s̄)` of
`Numlib.Analysis.Calculus.ContDiffOnClosure`); the extra generality — derivatives *within* a set
that need not be open, and an extension target that need not be the closure — is what the
induction on the order needs: on `Ω ×ˢ [0, ∞)` the derivatives at `t = 0` are one-sided, and the
extension is to `closure Ω ×ˢ [0, ∞)`, not to the closure of the product.

## Main results

* `hasFDerivWithinAt_prod_of_partials`: a function on `E × ℝ` with a partial Fréchet derivative
  in `x` at every point of `Ω ×ˢ s`, jointly continuous on `Ω ×ˢ s`, and a partial derivative in
  `t` within `s`, is differentiable within `Ω ×ˢ s`, with derivative
  `prodFDerivL (fx p, ft p) : (y, τ) ↦ fx p y + τ • ft p`. Only the `x`-partial needs to be
  continuous; the argument is the classical one, a mean value inequality on a segment in `Ω`.
* `ContDiffOnExtendsTo.prod_succ`: **the induction step** — if `f` extends continuously to `t`,
  and its two partial derivatives are of class `ContDiffOnExtendsTo ℝ n` on `Ω ×ˢ s` with
  extensions to `t`, then so is `f` at order `n + 1`.
* `contDiffOnExtendsTo_prod_of_partials`: **the theorem** — a family `g i j : E × ℝ → E [×i]→L F`
  of candidate partial derivatives `∂ₜ^j D_x^i f`, `i + j ≤ k`, each continuous on `t ⊇ Ω ×ˢ s`,
  with `g (i + 1) j` the `x`-derivative of `g i j` (curried) and `g i (j + 1)` its `t`-derivative
  within `s`, makes `g 0 0` of class `ContDiffOnExtendsTo ℝ k` on `Ω ×ˢ s` with extensions to `t`.
  The symmetry of the mixed partials is built into the hypotheses, since `g (i + 1) (j + 1)` is
  reached from `g i j` either way.

## References

[brezis2011functional], chapter 9 footnote 16 (the class `C^k(Ω̄)`), §10.1 Theorem 10.1 (5).
-/

open Filter Set Topology

open scoped ContDiff

/-! ### The class `C^n` on `s` with derivatives extending continuously to `t` -/

section ExtendsTo

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {X F G : Type*} [NormedAddCommGroup X]
  [NormedSpace 𝕜 X] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G]
  [NormedSpace 𝕜 G]

/-- **The class `C^n` on `s` with derivatives extending continuously to `t`**: `f` is `C^n` on
`s` and each iterated derivative within `s`, `iteratedFDerivWithin 𝕜 m f s` for `m ≤ n`, agrees on
`s` with a function continuous on `t`. For `s` open and `t = closure s` this is the class
`C^n(s̄)` of `ContDiffOnClosure`; the derivatives are taken *within* `s` so that `s` may have a
boundary in some directions (the half cylinder `Ω ×ˢ Ici 0`), and `t` is arbitrary so that the
extension may be asked on a set smaller than the closure (`closure Ω ×ˢ Ioi 0`). -/
def ContDiffOnExtendsTo (n : WithTop ℕ∞) (f : X → F) (s t : Set X) : Prop :=
  ContDiffOn 𝕜 n f s ∧ ∀ m : ℕ, (m : WithTop ℕ∞) ≤ n →
    ∃ g : X → X [×m]→L[𝕜] F, ContinuousOn g t ∧ EqOn g (iteratedFDerivWithin 𝕜 m f s) s

variable {𝕜} {n : WithTop ℕ∞} {f : X → F} {s t : Set X}

namespace ContDiffOnExtendsTo

/-- A function of the class is `C^n` on `s`. -/
theorem contDiffOn (h : ContDiffOnExtendsTo 𝕜 n f s t) : ContDiffOn 𝕜 n f s := h.1

/-- A function of the class is continuous on `s`. -/
theorem continuousOn (h : ContDiffOnExtendsTo 𝕜 n f s t) : ContinuousOn f s :=
  h.1.continuousOn

/-- The derivative of order `m ≤ n` within `s` extends continuously to `t`. -/
theorem exists_continuousOn_eqOn_iteratedFDerivWithin (h : ContDiffOnExtendsTo 𝕜 n f s t)
    {m : ℕ} (hm : (m : WithTop ℕ∞) ≤ n) :
    ∃ g : X → X [×m]→L[𝕜] F, ContinuousOn g t ∧ EqOn g (iteratedFDerivWithin 𝕜 m f s) s :=
  h.2 m hm

/-- Monotonicity in the order. -/
theorem of_le {m : WithTop ℕ∞} (h : ContDiffOnExtendsTo 𝕜 n f s t) (hmn : m ≤ n) :
    ContDiffOnExtendsTo 𝕜 m f s t :=
  ⟨h.1.of_le hmn, fun k hk ↦ h.2 k (hk.trans hmn)⟩

/-- Monotonicity in the extension target. -/
theorem mono_right {t' : Set X} (h : ContDiffOnExtendsTo 𝕜 n f s t) (ht : t' ⊆ t) :
    ContDiffOnExtendsTo 𝕜 n f s t' :=
  ⟨h.1, fun m hm ↦
    let ⟨g, hgc, hge⟩ := h.2 m hm
    ⟨g, hgc.mono ht, hge⟩⟩

/-- The class depends only on the values on `s`. -/
theorem congr {f₁ : X → F} (h : ContDiffOnExtendsTo 𝕜 n f s t) (hf : EqOn f₁ f s) :
    ContDiffOnExtendsTo 𝕜 n f₁ s t :=
  ⟨h.1.congr hf, fun m hm ↦
    let ⟨g, hgc, hge⟩ := h.2 m hm
    ⟨g, hgc, fun x hx ↦ by rw [iteratedFDerivWithin_congr hf hx]; exact hge hx⟩⟩

/-- The function itself extends continuously to `t`. -/
theorem exists_continuousOn_eqOn (h : ContDiffOnExtendsTo 𝕜 n f s t) :
    ∃ g : X → F, ContinuousOn g t ∧ EqOn g f s := by
  obtain ⟨g₀, hgc, hge⟩ := h.2 0 (by simp)
  refine ⟨fun x ↦ continuousMultilinearCurryFin0 𝕜 X F (g₀ x),
    (continuousMultilinearCurryFin0 𝕜 X F).continuous.comp_continuousOn hgc, fun x hx ↦ ?_⟩
  change continuousMultilinearCurryFin0 𝕜 X F (g₀ x) = f x
  rw [hge hx, iteratedFDerivWithin_zero_eq_comp, Function.comp_apply]
  exact (continuousMultilinearCurryFin0 𝕜 X F).apply_symm_apply (f x)

/-- Composition with a continuous linear map. -/
theorem continuousLinearMap_comp (h : ContDiffOnExtendsTo 𝕜 n f s t) (L : F →L[𝕜] G)
    (hs : UniqueDiffOn 𝕜 s) : ContDiffOnExtendsTo 𝕜 n (L ∘ f) s t :=
  ⟨h.contDiffOn.continuousLinearMap_comp L, fun m hm ↦
    let ⟨g, hgc, hge⟩ := h.2 m hm
    ⟨fun x ↦ L.compContinuousMultilinearMap (g x),
      (ContinuousLinearMap.compContinuousMultilinearMapL 𝕜 (fun _ : Fin m ↦ X) F G L)
        |>.continuous.comp_continuousOn hgc,
      fun x hx ↦ by
        rw [L.iteratedFDerivWithin_comp_left (h.1 x hx) hs hx hm]
        exact congrArg _ (hge hx)⟩⟩

/-- Sums. -/
theorem add {g : X → F} (hf : ContDiffOnExtendsTo 𝕜 n f s t)
    (hg : ContDiffOnExtendsTo 𝕜 n g s t) (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOnExtendsTo 𝕜 n (f + g) s t :=
  ⟨hf.contDiffOn.add hg.contDiffOn, fun m hm ↦
    let ⟨Gf, hGfc, hGfe⟩ := hf.2 m hm
    let ⟨Gg, hGgc, hGge⟩ := hg.2 m hm
    ⟨Gf + Gg, hGfc.add hGgc, fun x hx ↦ by
      rw [Pi.add_apply, iteratedFDerivWithin_add_apply ((hf.1 x hx).of_le hm)
        ((hg.1 x hx).of_le hm) hs hx, hGfe hx, hGge hx]⟩⟩

/-- Pairs. -/
theorem prodMk {g : X → G} (hf : ContDiffOnExtendsTo 𝕜 n f s t)
    (hg : ContDiffOnExtendsTo 𝕜 n g s t) (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOnExtendsTo 𝕜 n (fun x ↦ (f x, g x)) s t :=
  ⟨hf.contDiffOn.prodMk hg.contDiffOn, fun m hm ↦
    let ⟨Gf, hGfc, hGfe⟩ := hf.2 m hm
    let ⟨Gg, hGgc, hGge⟩ := hg.2 m hm
    ⟨fun x ↦ (Gf x).prod (Gg x),
      (ContinuousMultilinearMap.prodL 𝕜 (fun _ : Fin m ↦ X) F G).continuous.comp_continuousOn
        (hGfc.prodMk hGgc),
      fun x hx ↦ by
        simp only [iteratedFDerivWithin_prodMk (hf.1 x hx) (hg.1 x hx) hs hx hm, hGfe hx,
          hGge hx]⟩⟩

/-- **From derivatives within `s` to `C^n(s̄')` on an open subset**: if the derivatives of `f`
within `s` extend continuously to `t`, then on every open `s' ⊆ s` with `closure s' ⊆ t` the
function is of class `C^n(s̄')` in the sense of `ContDiffOnClosure` — on the open set `s'` the
derivatives within `s` are the ordinary ones. -/
theorem contDiffOnClosure {s' : Set X} (h : ContDiffOnExtendsTo 𝕜 n f s t) (hs' : IsOpen s')
    (hs's : s' ⊆ s) (hst : closure s' ⊆ t) : ContDiffOnClosure 𝕜 n f s' :=
  ⟨h.1.mono hs's, fun m hm ↦
    let ⟨g, hgc, hge⟩ := h.2 m hm
    ⟨g, hgc.mono hst, fun x hx ↦ by
      rw [hge (hs's hx), ← iteratedFDerivWithin_inter_open hs' hx, inter_eq_right.2 hs's,
        iteratedFDerivWithin_of_isOpen m hs' hx]⟩⟩

end ContDiffOnExtendsTo

/-- At order `0` the class is continuity on `s` with a continuous extension to `t`. -/
theorem contDiffOnExtendsTo_zero_iff :
    ContDiffOnExtendsTo 𝕜 0 f s t ↔
      ContinuousOn f s ∧ ∃ g : X → F, ContinuousOn g t ∧ EqOn g f s := by
  constructor
  · intro h
    exact ⟨h.continuousOn, h.exists_continuousOn_eqOn⟩
  · rintro ⟨hf, g, hgc, hge⟩
    refine ⟨contDiffOn_zero.2 hf, fun m hm ↦ ?_⟩
    obtain rfl : m = 0 := by exact_mod_cast le_zero_iff.1 hm
    refine ⟨fun x ↦ (continuousMultilinearCurryFin0 𝕜 X F).symm (g x),
      (continuousMultilinearCurryFin0 𝕜 X F).symm.continuous.comp_continuousOn hgc,
      fun x hx ↦ ?_⟩
    simp only [iteratedFDerivWithin_zero_eq_comp, Function.comp_apply, hge hx]

/-- `C^∞` with extensions is `C^n` with extensions for every finite `n`. -/
theorem contDiffOnExtendsTo_infty_iff :
    ContDiffOnExtendsTo 𝕜 ∞ f s t ↔ ∀ n : ℕ, ContDiffOnExtendsTo 𝕜 n f s t := by
  constructor
  · exact fun h n ↦ h.of_le (by simp)
  · intro h
    exact ⟨contDiffOn_infty.2 fun n ↦ (h n).1, fun m _ ↦ (h m).2 m le_rfl⟩

/-- A function of class `C^n(s̄)` with `s` open is of class `C^n` on `s` with derivatives
extending to `closure s`, and conversely. -/
theorem contDiffOnExtendsTo_closure_iff_contDiffOnClosure (hs : IsOpen s) :
    ContDiffOnExtendsTo 𝕜 n f s (closure s) ↔ ContDiffOnClosure 𝕜 n f s := by
  refine ⟨fun h ↦ h.contDiffOnClosure hs subset_rfl subset_rfl, fun h ↦ ⟨h.1, fun m hm ↦ ?_⟩⟩
  obtain ⟨g, hgc, hge⟩ := h.2 m hm
  exact ⟨g, hgc, fun x hx ↦ by rw [iteratedFDerivWithin_of_isOpen m hs hx]; exact hge hx⟩

end ExtendsTo

/-! ### Differentiability on `E × ℝ` from the two partial derivatives -/

section Prod

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

open ContinuousLinearMap in
/-- **The derivative on `E × ℝ` assembled from the two partial derivatives**, as a continuous
linear map of the pair `(A, b)`: `prodFDerivL (A, b) (y, τ) = A y + τ • b`. -/
noncomputable def prodFDerivL (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] : (E →L[ℝ] F) × F →L[ℝ] (E × ℝ →L[ℝ] F) :=
  ((compL ℝ (E × ℝ) E F).flip (fst ℝ E ℝ)).comp (ContinuousLinearMap.fst ℝ (E →L[ℝ] F) F) +
    (smulRightL ℝ (E × ℝ) F (snd ℝ E ℝ)).comp (ContinuousLinearMap.snd ℝ (E →L[ℝ] F) F)

/-- `prodFDerivL (A, b) (y, τ) = A y + τ • b`. -/
@[simp]
theorem prodFDerivL_apply (A : E →L[ℝ] F) (b : F) (q : E × ℝ) :
    prodFDerivL E F (A, b) q = A q.1 + q.2 • b := by
  simp [prodFDerivL]

/-- **The mean value step**: if `y ↦ f (y, t)` has derivative `fx (y, t)` on `Ω` and `fx` is
continuous within `Ω ×ˢ s` at `(x₀, t₀)`, then `f (x, t) − f (x₀, t) − fx (x₀, t₀) (x − x₀)` is
`o(‖x − x₀‖)` as `(x, t) → (x₀, t₀)` within `Ω ×ˢ s`: the mean value inequality on the segment
`[x₀, x]`, which lies in `Ω` for `x` close to `x₀`, with the bound `sup ‖fx (y, t) − fx (x₀, t₀)‖`
over the segment. (Mathlib's `isLittleO_sub_sub_fderiv` is this statement, but it is not
exported from its module.) -/
theorem isLittleO_sub_sub_fst_of_partial {Ω : Set E} (hΩ : IsOpen Ω) {s : Set ℝ}
    {f : E × ℝ → F} {fx : E × ℝ → E →L[ℝ] F}
    (hfx : ∀ x ∈ Ω, ∀ t ∈ s, HasFDerivAt (fun y ↦ f (y, t)) (fx (x, t)) x)
    {x₀ : E} {t₀ : ℝ} (hx₀ : x₀ ∈ Ω) (hfxc : ContinuousWithinAt fx (Ω ×ˢ s) (x₀, t₀)) :
    (fun q : E × ℝ ↦ f (q.1, q.2) - f (x₀, q.2) - fx (x₀, t₀) (q.1 - x₀))
      =o[𝓝[Ω ×ˢ s] (x₀, t₀)] fun q ↦ q.1 - x₀ := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hΩ x₀ hx₀
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousWithinAt_iff.1 hfxc ε hε
  have hmem : Metric.ball (x₀, t₀) (min δ r) ∈ 𝓝[Ω ×ˢ s] (x₀, t₀) :=
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ (lt_min hδ hr))
  filter_upwards [hmem, self_mem_nhdsWithin] with q hq hqs
  obtain ⟨x, t⟩ := q
  obtain ⟨hxΩ, hts⟩ := hqs
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff] at hq
  have hxr : x ∈ Metric.ball x₀ r := lt_of_lt_of_le hq.1 (min_le_right _ _)
  have hsegΩ : segment ℝ x₀ x ⊆ Ω :=
    ((convex_ball x₀ r).segment_subset (Metric.mem_ball_self hr) hxr).trans hball
  have hsegδ : ∀ y ∈ segment ℝ x₀ x, dist y x₀ < δ := by
    intro y hy
    have : y ∈ Metric.closedBall x₀ (dist x x₀) :=
      (convex_closedBall x₀ (dist x x₀)).segment_subset (Metric.mem_closedBall_self dist_nonneg)
        (Metric.mem_closedBall.2 le_rfl) hy
    exact (Metric.mem_closedBall.1 this).trans_lt (hq.1.trans_le (min_le_left _ _))
  have hbound : ∀ y ∈ segment ℝ x₀ x, ‖fx (y, t) - fx (x₀, t₀)‖ ≤ ε := by
    intro y hy
    have h := @hδε (y, t) ⟨hsegΩ hy, hts⟩ (by
      rw [Prod.dist_eq, max_lt_iff]
      exact ⟨hsegδ y hy, hq.2.trans_le (min_le_left _ _)⟩)
    rw [dist_eq_norm] at h
    exact h.le
  exact (convex_segment x₀ x).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (f := fun y ↦ f (y, t)) (f' := fun y ↦ fx (y, t))
    (fun y hy ↦ (hfx y (hsegΩ hy) t hts).hasFDerivWithinAt) hbound (left_mem_segment ℝ x₀ x)
    (right_mem_segment ℝ x₀ x)

/-- **Differentiability on `Ω ×ˢ s` from the partial derivatives**: let `Ω ⊆ E` be open and
`s ⊆ ℝ`; if `f : E × ℝ → F` has at every `(x, t) ∈ Ω ×ˢ s` the partial Fréchet derivative
`fx (x, t)` in `x` and the partial derivative `ft (x, t)` in `t` within `s`, and `fx` is jointly
continuous on `Ω ×ˢ s`, then `f` is differentiable within `Ω ×ˢ s` at every point, with derivative
`(y, τ) ↦ fx p y + τ • ft p`. Only the partial derivative in `x` is required to be continuous:
the increment `f (x, t) − f (x₀, t)` is controlled by the mean value inequality on the segment
`[x₀, x] ⊆ Ω` (`isLittleO_sub_sub_fst_of_partial`), the increment `f (x₀, t) − f (x₀, t₀)` by
the derivative in `t` at the point. -/
theorem hasFDerivWithinAt_prod_of_partials {Ω : Set E} (hΩ : IsOpen Ω) {s : Set ℝ}
    {f : E × ℝ → F} {fx : E × ℝ → E →L[ℝ] F} {ft : E × ℝ → F}
    (hfx : ∀ x ∈ Ω, ∀ t ∈ s, HasFDerivAt (fun y ↦ f (y, t)) (fx (x, t)) x)
    (hft : ∀ x ∈ Ω, ∀ t ∈ s, HasDerivWithinAt (fun r ↦ f (x, r)) (ft (x, t)) s t)
    (hfxc : ContinuousOn fx (Ω ×ˢ s)) {p : E × ℝ} (hp : p ∈ Ω ×ˢ s) :
    HasFDerivWithinAt f (prodFDerivL E F (fx p, ft p)) (Ω ×ˢ s) p := by
  obtain ⟨x₀, t₀⟩ := p
  obtain ⟨hx₀, ht₀⟩ : x₀ ∈ Ω ∧ t₀ ∈ s := hp
  -- the increment in the second variable
  have h2 : HasFDerivWithinAt (fun q : E × ℝ ↦ f (x₀, q.2))
      ((ContinuousLinearMap.snd ℝ E ℝ).smulRight (ft (x₀, t₀))) (Ω ×ˢ s) (x₀, t₀) := by
    have h := (hft x₀ hx₀ t₀ ht₀).hasFDerivWithinAt.comp (x₀, t₀)
      (hasFDerivWithinAt_snd (𝕜 := ℝ) (s := Ω ×ˢ s) (p := (x₀, t₀)))
      (fun q (hq : q ∈ Ω ×ˢ s) ↦ hq.2)
    exact h.congr_fderiv (by ext <;> simp)
  -- the increment in the first variable
  have h1 := isLittleO_sub_sub_fst_of_partial hΩ hfx hx₀ (hfxc (x₀, t₀) ⟨hx₀, ht₀⟩)
  have h1' : HasFDerivWithinAt (fun q : E × ℝ ↦ f q - f (x₀, q.2))
      ((fx (x₀, t₀)).comp (ContinuousLinearMap.fst ℝ E ℝ)) (Ω ×ˢ s) (x₀, t₀) := by
    rw [hasFDerivWithinAt_iff_isLittleO]
    refine (h1.congr_left fun q ↦ ?_).trans_isBigO (Asymptotics.isBigO_of_le _ fun q ↦ ?_)
    · simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', Prod.fst_sub]
      abel
    · exact (norm_fst_le (q - (x₀, t₀))).trans_eq' (by simp)
  have := h1'.add h2
  convert this using 1
  · ext q
    simp
  · ext <;> simp

end Prod

/-! ### The induction on the order -/

section Induction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {Ω : Set E} {s : Set ℝ} {t : Set (E × ℝ)}

/-- **The induction step: `C^{n+1}` from partial derivatives of class `C^n`, up to the
boundary.** Let `Ω ⊆ E` be open and `s ⊆ ℝ` uniquely differentiable. If `f : E × ℝ → F` is
continuous on `Ω ×ˢ s` with a continuous extension to `t`, has at every point of `Ω ×ˢ s` the
partial derivatives `fx` in `x` and `ft` in `t` (within `s`), and `fx`, `ft` are of class `C^n`
on `Ω ×ˢ s` with derivatives extending continuously to `t`, then `f` is of class `C^{n+1}` on
`Ω ×ˢ s` with derivatives extending continuously to `t`. The derivative of `f` within `Ω ×ˢ s` is
`prodFDerivL (fx p, ft p)` (`hasFDerivWithinAt_prod_of_partials`), a continuous linear image of
the pair `(fx, ft)`, and `iteratedFDerivWithin (m + 1) f` is the curried
`iteratedFDerivWithin m (fderivWithin f)`. -/
theorem ContDiffOnExtendsTo.prod_succ (hΩ : IsOpen Ω) (hs : UniqueDiffOn ℝ s) {n : ℕ}
    {f : E × ℝ → F} {fx : E × ℝ → E →L[ℝ] F} {ft : E × ℝ → F}
    (hf : ContDiffOnExtendsTo ℝ 0 f (Ω ×ˢ s) t)
    (hfx : ∀ x ∈ Ω, ∀ t ∈ s, HasFDerivAt (fun y ↦ f (y, t)) (fx (x, t)) x)
    (hft : ∀ x ∈ Ω, ∀ t ∈ s, HasDerivWithinAt (fun r ↦ f (x, r)) (ft (x, t)) s t)
    (hfxn : ContDiffOnExtendsTo ℝ n fx (Ω ×ˢ s) t)
    (hftn : ContDiffOnExtendsTo ℝ n ft (Ω ×ˢ s) t) :
    ContDiffOnExtendsTo ℝ (n + 1) f (Ω ×ˢ s) t := by
  have hsu : UniqueDiffOn ℝ (Ω ×ˢ s) := UniqueDiffOn.prod hΩ.uniqueDiffOn hs
  have hd : ∀ p ∈ Ω ×ˢ s, HasFDerivWithinAt f (prodFDerivL E F (fx p, ft p)) (Ω ×ˢ s) p :=
    fun p hp ↦ hasFDerivWithinAt_prod_of_partials hΩ hfx hft hfxn.continuousOn hp
  have hfd : EqOn (fderivWithin ℝ f (Ω ×ˢ s)) (fun p ↦ prodFDerivL E F (fx p, ft p)) (Ω ×ˢ s) :=
    fun p hp ↦ (hd p hp).fderivWithin (hsu p hp)
  have hD : ContDiffOnExtendsTo ℝ n (fderivWithin ℝ f (Ω ×ˢ s)) (Ω ×ˢ s) t :=
    ((hfxn.prodMk hftn hsu).continuousLinearMap_comp (prodFDerivL E F) hsu).congr hfd
  refine ⟨?_, fun m hm ↦ ?_⟩
  · rw [contDiffOn_succ_iff_fderivWithin hsu]
    exact ⟨fun p hp ↦ (hd p hp).differentiableWithinAt, by simp, hD.contDiffOn⟩
  · cases m with
    | zero => exact hf.2 0 le_rfl
    | succ m =>
      obtain ⟨g, hgc, hge⟩ := hD.2 m (by exact_mod_cast Nat.le_of_lt_succ (by exact_mod_cast hm))
      refine ⟨fun p ↦ (continuousMultilinearCurryRightEquiv' ℝ m (E × ℝ) F).symm (g p),
        (continuousMultilinearCurryRightEquiv' ℝ m (E × ℝ) F).symm.continuous.comp_continuousOn
          hgc, fun p hp ↦ ?_⟩
      rw [iteratedFDerivWithin_succ_eq_comp_right hsu hp, Function.comp_apply]
      exact congrArg _ (hge hp)

/-- **Smoothness on `Ω ×ˢ s` from a family of partial derivatives, up to the boundary.** Let
`Ω ⊆ E` be open, `s ⊆ ℝ` uniquely differentiable, `Ω ×ˢ s ⊆ t`, and let
`g i j : E × ℝ → E [×i]→L[ℝ] F` be candidates for the partial derivatives `∂ₜ^j D_x^i f` of
`f = g 0 0` (read in `F`), for `i + j ≤ k`: each `g i j` is continuous on `t`, the `x`-derivative
of `g i j (·, t)` at `x ∈ Ω` is `g (i + 1) j (x, t)` curried in its first argument, and the
`t`-derivative of `g i j (x, ·)` within `s` at `t ∈ s` is `g i (j + 1) (x, t)`. Then every `g i j`
with `i + j + n ≤ k` is of class `C^n` on `Ω ×ˢ s` with derivatives extending continuously to
`t`; in particular `g 0 0` is of class `C^k`. Induction on `n` through
`ContDiffOnExtendsTo.prod_succ`. The symmetry of the mixed partial derivatives is part of the
hypotheses, since `g (i + 1) (j + 1)` is reached from `g i j` either way. -/
theorem contDiffOnExtendsTo_prod_of_partials (hΩ : IsOpen Ω) (hs : UniqueDiffOn ℝ s)
    (hst : Ω ×ˢ s ⊆ t) {k : ℕ} {g : (i : ℕ) → ℕ → E × ℝ → E [×i]→L[ℝ] F}
    (hgc : ∀ i j, i + j ≤ k → ContinuousOn (g i j) t)
    (hgx : ∀ i j, i + 1 + j ≤ k → ∀ x ∈ Ω, ∀ t ∈ s, HasFDerivAt (fun y ↦ g i j (y, t))
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) ↦ E) F (g (i + 1) j (x, t))) x)
    (hgt : ∀ i j, i + (j + 1) ≤ k → ∀ x ∈ Ω, ∀ t ∈ s,
      HasDerivWithinAt (fun r ↦ g i j (x, r)) (g i (j + 1) (x, t)) s t) :
    ∀ n i j, i + j + n ≤ k → ContDiffOnExtendsTo ℝ n (g i j) (Ω ×ˢ s) t := by
  intro n
  induction n with
  | zero =>
    intro i j hij
    exact contDiffOnExtendsTo_zero_iff.2
      ⟨(hgc i j (by omega)).mono hst, g i j, hgc i j (by omega), fun _ _ ↦ rfl⟩
  | succ n ih =>
    intro i j hij
    refine ContDiffOnExtendsTo.prod_succ hΩ hs
      (fx := fun p ↦ continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) ↦ E) F
        (g (i + 1) j p))
      (contDiffOnExtendsTo_zero_iff.2
        ⟨(hgc i j (by omega)).mono hst, g i j, hgc i j (by omega), fun _ _ ↦ rfl⟩)
      (hgx i j (by omega)) (hgt i j (by omega)) ?_ (ih i (j + 1) (by omega))
    exact (ih (i + 1) j (by omega)).continuousLinearMap_comp
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) ↦ E) F).toContinuousLinearEquiv
        : (E [×(i + 1)]→L[ℝ] F) →L[ℝ] (E →L[ℝ] E [×i]→L[ℝ] F))
      (UniqueDiffOn.prod hΩ.uniqueDiffOn hs)

end Induction
