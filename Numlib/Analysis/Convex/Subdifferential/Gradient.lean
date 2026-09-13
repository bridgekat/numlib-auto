import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Numlib.Analysis.Convex.Subdifferential.Defs

/-!
# Gradients and the subdifferential

Where a convex function is differentiable its gradient is its only subgradient, and the directional
derivative is the corresponding linear function. Conversely, for a convex function finite at `x`,
differentiability at `x` is *equivalent* to linearity of `f'(x; ·)`, and in finite dimensions the
two-sided derivatives along the vectors of a basis already suffice.

Dually, a point of `epi f*` is *exposed* exactly when it is `(y, f* y)` for a `y` that is the only
subgradient of `f` somewhere, and the same holds for the set cut out by a positively homogeneous
function. Both are phrased in terms of unique subgradients rather than of differentiability: the
converse passage needs `x` interior to `dom f` and is in `Subdifferential/Uniqueness.lean`.

## Main results

* `subdifferential_eq_singleton_of_dirDeriv_eq`, `clFn_dirDeriv_eq_of_subdifferential_eq_singleton`
  — if `f'(x; ·)` is `⟨·, y₀⟩` then `∂f x = {y₀}`, and conversely a single-valued `∂f x` makes
  `cl f'(x; ·)` linear.
* `le_hasFDerivAt`, `subdifferential_eq_singleton_of_hasFDerivAt` — the gradient inequality
  `f z ≥ f x + ⟨z - x, ∇f x⟩`, and `∂f x = {∇f x}` ([rockafellar1970convex] Theorem 25.1). The
  uniqueness half alone, `eq_of_mem_subdifferential_of_hasFDerivAt`, needs no convexity.
* `differentiableAtFn_iff_exists_dirDeriv_eq`, `differentiableAtFn_of_forall_basis_dirDeriv_eq` —
  differentiability is linearity of `f'(x; ·)`, already along a basis
  ([rockafellar1970convex] Theorem 25.2).
* `mem_exposedPoints_epi_conj_iff`, `mem_exposedPoints_supportSet_iff` — exposed points as unique
  subgradients.
* `HasGradientAtFn`, `DifferentiableAtFn` — `∇f x = f'` for an `EReal`-valued `f`, with the results
  above repackaged as `.le`, `.subdifferential_eq`, `.dirDeriv_eq`, `.mem_interior_dom`, `.proper`
  and `.unique`. This is the interface the Legendre theory uses.

## Implementation notes

Differentiability of an `EReal`-valued function is carried by a local real representative:
`HasFDerivAt` needs a normed target, so a convex `f : E → EReal` is differentiable at `x` when some
real `g` has `f =ᶠ[𝓝 x] fun z => (g z : EReal)` and `HasFDerivAt g f' x`. This forces
`x ∈ int (dom f)`, the standing assumption that `f x` is finite. Restricting to `f : E → ℝ` instead
would lose the Legendre theory, where the interesting functions are `+∞` outside an open set.

The directional-derivative statements hold over an arbitrary pairing `B`, with uniqueness needing
`B` separating in its second variable. In place of `[FiniteDimensional ℝ E]` the exposed point
results assume `[IsCompatiblePairing B.flip]` — every continuous linear functional on `F` is
`⟨x, ·⟩` — which holds for finite-dimensional `E` paired with `StrongDual ℝ E`.

## References

* [rockafellar1970convex] §25.
-/

open Set Filter Topology

namespace ConvexAnalysis

/-! ### The algebraic core: a linear directional derivative -/

section Linear

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {x : E}

/-- Algebraically: if the directional derivative `f'(x; ·)` is the linear function `⟨·, y₀⟩`, then
`y₀` is the unique subgradient of `f` at `x`. This is the description of `∂f x` by
`⟨·, y⟩ ≤ f'(x; ·)` plus the observation that `⟨v, y⟩ ≤ ⟨v, y₀⟩` for *every* `v`, `-v` included,
forces `⟨·, y⟩ = ⟨·, y₀⟩`; the pairing must therefore separate the points of `F`. -/
theorem subdifferential_eq_singleton_of_dirDeriv_eq (hsep : Function.Injective B.flip)
    (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) {y₀ : F}
    (h : ∀ v : E, dirDeriv f x v = ((B v y₀ : ℝ) : EReal)) :
    subdifferential B f x = {y₀} := by
  ext y
  rw [mem_subdifferential_iff_le_dirDeriv ht hb, Set.mem_singleton_iff]
  constructor
  · intro hy
    refine hsep (LinearMap.ext fun v => ?_)
    have h₁ : B v y ≤ B v y₀ := by
      have hv := hy v
      rw [h v, EReal.coe_le_coe_iff] at hv
      exact hv
    have h₂ : B (-v) y ≤ B (-v) y₀ := by
      have hv := hy (-v)
      rw [h (-v), EReal.coe_le_coe_iff] at hv
      exact hv
    rw [map_neg, LinearMap.neg_apply, LinearMap.neg_apply] at h₂
    simp only [LinearMap.flip_apply]
    linarith
  · rintro rfl v
    rw [h v]

/-- The converse at the level of closures: if `∂f x` is a single point `y₀`, then `cl f'(x; ·)` is
the linear function `⟨·, y₀⟩`. It is `cl f'(x; ·) = δ*(· | ∂f x)`, the support function of a
singleton being linear. -/
theorem clFn_dirDeriv_eq_of_subdifferential_eq_singleton [TopologicalSpace E] [ContinuousSMul ℝ E]
    [IsTopologicalAddGroup E] [LocallyConvexSpace ℝ E] [IsCompatiblePairing B] (hf : ConvexFn f)
    (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) {y₀ : F} (h : subdifferential B f x = {y₀}) :
    clFn (dirDeriv f x) = fun v => ((B v y₀ : ℝ) : EReal) := by
  rw [clFn_dirDeriv (B := B) hf ht hb, h, supportFn_singleton]
  rfl

end Linear

/-! ### Rays and difference quotients -/

section Frechet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → EReal} {g : E → ℝ}
  {x : E} {f' : E →L[ℝ] ℝ}

/-- The ray `t ↦ x + t • v` tends to `x` as `t ↓ 0`. -/
theorem tendsto_ray_nhdsGT (x v : E) :
    Tendsto (fun t : ℝ => x + t • v) (𝓝[>] (0 : ℝ)) (𝓝 x) := by
  have hc : Continuous fun t : ℝ => x + t • v := by fun_prop
  simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

/-- The difference quotient along a ray converges to the derivative in that direction. This is the
only piece of calculus the section uses. -/
theorem tendsto_slope_ray_of_hasFDerivAt (hd : HasFDerivAt g f' x) (v : E) :
    Tendsto (fun t : ℝ => (g (x + t • v) - g x) / t) (𝓝[>] (0 : ℝ)) (𝓝 (f' v)) := by
  have hsmul : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa using HasDerivAt.smul_const (hasDerivAt_id (0 : ℝ)) v
  have hcurve : HasDerivAt (fun t : ℝ => x + t • v) v 0 := HasDerivAt.const_add x hsmul
  have hd' : HasFDerivAt g f' ((fun t : ℝ => x + t • v) 0) := by simpa using hd
  have hcomp : HasDerivAt (fun t : ℝ => g (x + t • v)) (f' v) 0 := by
    simpa [Function.comp_def] using HasFDerivAt.comp_hasDerivAt 0 hd' hcurve
  have hmono : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) := nhdsWithin_mono _ fun t ht => ne_of_gt ht
  refine ((hasDerivAt_iff_tendsto_slope.1 hcomp).mono_left hmono).congr fun t => ?_
  simp [slope_def_field]

/-! ### Local finiteness and properness -/

omit [NormedSpace ℝ E] in
/-- A function that agrees with a real-valued function near `x` has `x` in the interior of its
effective domain. Neither convexity nor differentiability plays any role — only local
finiteness. -/
theorem mem_interior_dom_of_eventuallyEq_coe
    (hfg : f =ᶠ[𝓝 x] fun z => ((g z : ℝ) : EReal)) : x ∈ interior (dom f) :=
  mem_interior_iff_mem_nhds.2
    (hfg.mono fun z hz => mem_dom.2 (by rw [hz]; exact EReal.coe_lt_top _))

/-- A convex function that is finite near a point is proper. Unlike the general statement that a
convex function taking `−∞` takes it throughout the relative interior of its domain, this holds in
any topological vector space: if `f u = ⊥` then `f` is `⊥` on the half-open segment `[u, x)`,
whose points approach `x`, where `f` is finite. -/
theorem proper_of_eventuallyEq_coe (hf : ConvexFn f)
    (hfg : f =ᶠ[𝓝 x] fun z => ((g z : ℝ) : EReal)) : Proper f := by
  have hx : f x = ((g x : ℝ) : EReal) := hfg.self_of_nhds
  have hxdom : x ∈ dom f := mem_dom.2 (by rw [hx]; exact EReal.coe_lt_top _)
  refine ⟨⟨x, hxdom⟩, fun u hu => ?_⟩
  have hray : Tendsto (fun a : ℝ => (1 - a) • u + a • x) (𝓝[<] (1 : ℝ)) (𝓝 x) := by
    have hc : Continuous fun a : ℝ => (1 - a) • u + a • x := by fun_prop
    simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
  have hfin : ∀ᶠ z in 𝓝 x, f z ≠ ⊥ :=
    hfg.mono fun z hz => by rw [hz]; exact EReal.coe_ne_bot _
  have hne : ∀ᶠ a in 𝓝[<] (1 : ℝ), f ((1 - a) • u + a • x) ≠ ⊥ := hray.eventually hfin
  have hbot : ∀ᶠ a in 𝓝[<] (1 : ℝ), f ((1 - a) • u + a • x) = ⊥ := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds one_pos), self_mem_nhdsWithin]
      with a ha ha1
    exact hf.eq_bot_of_lt_one hu hxdom ha.le ha1
  obtain ⟨a, hane, hae⟩ := (hne.and hbot).exists
  exact hane hae

/-! ### The gradient is the unique subgradient -/

/-- **The gradient inequality**: a convex function lies above its tangent affine function at every
point of differentiability. -/
theorem le_of_hasFDerivAt (hf : ConvexFn f) (hp : Proper f)
    (hfg : f =ᶠ[𝓝 x] fun z => ((g z : ℝ) : EReal)) (hd : HasFDerivAt g f' x) (z : E) :
    f x + ((f' (z - x) : ℝ) : EReal) ≤ f z := by
  have hx : f x = ((g x : ℝ) : EReal) := hfg.self_of_nhds
  rcases eq_or_ne (f z) ⊤ with hz | hz
  · rw [hz]; exact le_top
  obtain ⟨r, hfz⟩ : ∃ r : ℝ, f z = ((r : ℝ) : EReal) :=
    ⟨(f z).toReal, (EReal.coe_toReal hz (hp.ne_bot z)).symm⟩
  have hIoc : Set.Ioc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := by
    rw [← Set.Ioi_inter_Iic]
    exact inter_mem_nhdsWithin _ (Iic_mem_nhds one_pos)
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), f (x + t • (z - x)) = ((g (x + t • (z - x)) : ℝ) : EReal) :=
    (tendsto_ray_nhdsGT x (z - x)).eventually hfg
  have hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ), (g (x + t • (z - x)) - g x) / t ≤ r - g x := by
    filter_upwards [hIoc, hev] with t ht hteq
    have hcombo := hf.epi_combo (x := x) (y := z) (μ := g x) (ν := r) hx.le hfz.le
      (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t) ht.1.le (by ring)
    have hpt : (1 - t) • x + t • z = x + t • (z - x) := by module
    rw [hpt, hteq, EReal.coe_le_coe_iff] at hcombo
    rw [div_le_iff₀ ht.1]
    nlinarith [hcombo]
  have hle := le_of_tendsto (tendsto_slope_ray_of_hasFDerivAt hd (z - x)) hbound
  rw [hx, hfz, ← EReal.coe_add, EReal.coe_le_coe_iff]
  linarith

/-- **Uniqueness**: any subgradient at a point of differentiability is the derivative. Neither
convexity nor properness is used — only the limit of the difference quotient along the two opposite
rays. -/
theorem eq_of_mem_subdifferential_of_hasFDerivAt (hfg : f =ᶠ[𝓝 x] fun z => ((g z : ℝ) : EReal))
    (hd : HasFDerivAt g f' x) {y : StrongDual ℝ E}
    (hy : y ∈ subdifferential (topDualPairing ℝ E).flip f x) : y = f' := by
  have hx : f x = ((g x : ℝ) : EReal) := hfg.self_of_nhds
  have hle : ∀ w : E, y w ≤ f' w := by
    intro w
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), f (x + t • w) = ((g (x + t • w) : ℝ) : EReal) :=
      (tendsto_ray_nhdsGT x w).eventually hfg
    have hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ), y w ≤ (g (x + t • w) - g x) / t := by
      filter_upwards [self_mem_nhdsWithin, hev] with t ht hteq
      have hsub := hy (x + t • w)
      have hval : ((topDualPairing ℝ E).flip (x + t • w - x)) y = t * y w := by
        rw [add_sub_cancel_left, LinearMap.flip_apply, topDualPairing_apply, map_smul,
          smul_eq_mul]
      rw [hval, hx, hteq, ← EReal.coe_add, EReal.coe_le_coe_iff] at hsub
      rw [le_div_iff₀ ht]
      linarith
    exact ge_of_tendsto (tendsto_slope_ray_of_hasFDerivAt hd w) hbound
  refine ContinuousLinearMap.ext fun w => le_antisymm (hle w) ?_
  have hneg := hle (-w)
  rw [map_neg, map_neg] at hneg
  linarith

/-- At a point where a convex function is differentiable, the gradient is the unique
subgradient. -/
theorem subdifferential_eq_singleton_of_hasFDerivAt (hf : ConvexFn f) (hp : Proper f)
    (hfg : f =ᶠ[𝓝 x] fun z => ((g z : ℝ) : EReal)) (hd : HasFDerivAt g f' x) :
    subdifferential (topDualPairing ℝ E).flip f x = {f'} := by
  refine Set.eq_singleton_iff_unique_mem.2 ⟨fun z => ?_, fun _ hy =>
    eq_of_mem_subdifferential_of_hasFDerivAt hfg hd hy⟩
  have hval : ((topDualPairing ℝ E).flip (z - x)) f' = f' (z - x) := rfl
  rw [hval]
  exact le_of_hasFDerivAt hf hp hfg hd z

/-- **Necessity**: at a point of differentiability the directional derivative is the linear
function `v ↦ ⟨v, ∇f x⟩`. Both halves come from the defining infimum: the lower bound is the
gradient inequality at `x + a • v`, the upper bound the limit `a ↓ 0`, extracted through
`EReal.lt_iff_exists_real_btwn` so that no `EReal` division has to be computed. -/
theorem dirDeriv_eq_of_hasFDerivAt (hf : ConvexFn f) (hp : Proper f)
    (hfg : f =ᶠ[𝓝 x] fun z => ((g z : ℝ) : EReal)) (hd : HasFDerivAt g f' x) (v : E) :
    dirDeriv f x v = ((f' v : ℝ) : EReal) := by
  have hx : f x = ((g x : ℝ) : EReal) := hfg.self_of_nhds
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), f (x + t • v) = ((g (x + t • v) : ℝ) : EReal) :=
    (tendsto_ray_nhdsGT x v).eventually hfg
  have key : ∀ m : ℝ, f' v < m → dirDeriv f x v ≤ ((m : ℝ) : EReal) := by
    intro m hm
    have hlt : ∀ᶠ t in 𝓝[>] (0 : ℝ), (g (x + t • v) - g x) / t < m :=
      (tendsto_slope_ray_of_hasFDerivAt hd v).eventually (Iio_mem_nhds hm)
    have hcomb : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧
        f (x + t • v) = ((g (x + t • v) : ℝ) : EReal) ∧ (g (x + t • v) - g x) / t < m := by
      filter_upwards [self_mem_nhdsWithin, hev, hlt] with t ht hteq htlt
      exact ⟨ht, hteq, htlt⟩
    obtain ⟨t, ht, hteq, htlt⟩ := hcomb.exists
    refine (dirDeriv_le f x v ht).trans ?_
    rw [hx, hteq, EReal.sub_div_le_coe_iff ht, EReal.coe_le_coe_iff]
    rw [div_lt_iff₀ ht] at htlt
    linarith
  refine le_antisymm ?_ (le_dirDeriv fun a ha => ?_)
  · by_contra hcon
    obtain ⟨m, hm1, hm2⟩ := EReal.lt_iff_exists_real_btwn.1 (not_le.1 hcon)
    exact absurd (key m (by exact_mod_cast hm1)) (not_le.2 hm2)
  · rw [hx, EReal.coe_le_sub_div_iff ha]
    have hgrad := le_of_hasFDerivAt hf hp hfg hd (x + a • v)
    rw [hx, add_sub_cancel_left, map_smul, smul_eq_mul, ← EReal.coe_add] at hgrad
    rwa [mul_comm (f' v) a]

/-! ### Packaging: `∇f` for an `EReal`-valued function -/

/-- `f` **has gradient** `f'` at `x`: near `x`, `f` agrees with a real-valued function that is
Fréchet differentiable at `x` with derivative `f'`. This is `∇f x = f'`. An `EReal`-valued function
cannot satisfy `HasFDerivAt` directly — that needs a normed target — and the local real
representative carries exactly what the classical definition presupposes: `f` finite near `x`. -/
def HasGradientAtFn (f : E → EReal) (f' : StrongDual ℝ E) (x : E) : Prop :=
  ∃ g : E → ℝ, f =ᶠ[𝓝 x] (fun z => ((g z : ℝ) : EReal)) ∧ HasFDerivAt g f' x

/-- `f` is **differentiable** at `x`: it has a gradient there. -/
def DifferentiableAtFn (f : E → EReal) (x : E) : Prop :=
  ∃ f' : StrongDual ℝ E, HasGradientAtFn f f' x

theorem hasGradientAtFn_coe (hd : HasFDerivAt g f' x) :
    HasGradientAtFn (fun z => ((g z : ℝ) : EReal)) f' x :=
  ⟨g, EventuallyEq.rfl, hd⟩

/-- Packaged: a gradient at `x` puts `x` in the interior of `dom f`. -/
theorem HasGradientAtFn.mem_interior_dom (h : HasGradientAtFn f f' x) : x ∈ interior (dom f) := by
  obtain ⟨g, hfg, -⟩ := h
  exact mem_interior_dom_of_eventuallyEq_coe hfg

/-- Packaged: a convex function with a gradient somewhere is proper. -/
theorem HasGradientAtFn.proper (hf : ConvexFn f) (h : HasGradientAtFn f f' x) : Proper f := by
  obtain ⟨g, hfg, -⟩ := h
  exact proper_of_eventuallyEq_coe hf hfg

/-- The gradient inequality, packaged. -/
theorem HasGradientAtFn.le (hf : ConvexFn f) (h : HasGradientAtFn f f' x) (z : E) :
    f x + ((f' (z - x) : ℝ) : EReal) ≤ f z := by
  obtain ⟨g, hfg, hd⟩ := h
  exact le_of_hasFDerivAt hf (proper_of_eventuallyEq_coe hf hfg) hfg hd z

/-- Packaged: the gradient is the only subgradient. -/
theorem HasGradientAtFn.subdifferential_eq (hf : ConvexFn f) (h : HasGradientAtFn f f' x) :
    subdifferential (topDualPairing ℝ E).flip f x = {f'} := by
  obtain ⟨g, hfg, hd⟩ := h
  exact subdifferential_eq_singleton_of_hasFDerivAt hf (proper_of_eventuallyEq_coe hf hfg) hfg hd

theorem HasGradientAtFn.mem_subdifferential (hf : ConvexFn f) (h : HasGradientAtFn f f' x) :
    f' ∈ subdifferential (topDualPairing ℝ E).flip f x := by
  rw [h.subdifferential_eq hf]
  exact Set.mem_singleton_iff.2 rfl

/-- Packaged: `f'(x; v) = ⟨v, ∇f x⟩` at a point of differentiability. -/
theorem HasGradientAtFn.dirDeriv_eq (hf : ConvexFn f) (h : HasGradientAtFn f f' x) (v : E) :
    dirDeriv f x v = ((f' v : ℝ) : EReal) := by
  obtain ⟨g, hfg, hd⟩ := h
  exact dirDeriv_eq_of_hasFDerivAt hf (proper_of_eventuallyEq_coe hf hfg) hfg hd v

/-- The gradient is unique where it exists. This is the
uniqueness of `HasFDerivAt` for the local real representative, and it needs no convexity. -/
theorem HasGradientAtFn.unique {f₁' f₂' : StrongDual ℝ E} (h₁ : HasGradientAtFn f f₁' x)
    (h₂ : HasGradientAtFn f f₂' x) : f₁' = f₂' := by
  obtain ⟨g₁, hfg₁, hd₁⟩ := h₁
  obtain ⟨g₂, hfg₂, hd₂⟩ := h₂
  have hgg : g₁ =ᶠ[𝓝 x] g₂ := by
    filter_upwards [hfg₁, hfg₂] with z h1 h2
    have h1' : f z = ((g₁ z : ℝ) : EReal) := h1
    have h2' : f z = ((g₂ z : ℝ) : EReal) := h2
    exact_mod_cast h1'.symm.trans h2'
  exact hd₁.unique (hd₂.congr_of_eventuallyEq hgg)

/-! ### From directional derivatives back to the gradient -/

section Sufficiency

variable {ι : Type*} [Finite ι]

/-- The **two-sided one-dimensional estimate** behind sufficiency. If the directional derivatives
of `f` at `x` along `v` and `-v` are `c` and `-c`, then for every `η > 0` there is a step `a₀ > 0`
with

```
f (x + t • v) ≤ f x + t * c + |t| * η        whenever |t| ≤ a₀,
```

for `t` of *either* sign. On the negative side the one-sided estimate is applied in the direction
`-v`; the linear term survives unchanged because `(-t) * (-c) = t * c`, while the error term picks
up `|t| = -t`. -/
theorem exists_forall_abs_le_of_dirDeriv_eq (hf : ConvexFn f) {r : ℝ} (hr : f x = (r : EReal))
    {v : E} {c η : ℝ} (hη : 0 < η) (hpos : dirDeriv f x v = (c : EReal))
    (hneg : dirDeriv f x (-v) = ((-c : ℝ) : EReal)) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ t : ℝ, |t| ≤ a₀ →
      f (x + t • v) ≤ ((r + t * c + |t| * η : ℝ) : EReal) := by
  obtain ⟨a₁, ha₁, h₁⟩ := exists_le_of_dirDeriv_lt hf hr (y := v) (m := c + η)
    (by rw [hpos]; exact_mod_cast lt_add_of_pos_right c hη)
  obtain ⟨a₂, ha₂, h₂⟩ := exists_le_of_dirDeriv_lt hf hr (y := -v) (m := -c + η)
    (by rw [hneg]; exact_mod_cast lt_add_of_pos_right (-c) hη)
  refine ⟨min a₁ a₂, lt_min ha₁ ha₂, fun t ht => ?_⟩
  rcases lt_trichotomy t 0 with hlt | rfl | hgt
  · have habs : |t| = -t := abs_of_neg hlt
    rw [habs] at ht
    have hle := h₂ (-t) (by linarith) (ht.trans (min_le_right _ _))
    rw [neg_smul_neg] at hle
    refine hle.trans (le_of_eq ?_)
    rw [EReal.coe_eq_coe_iff, habs]
    ring
  · rw [zero_smul, add_zero, hr, EReal.coe_le_coe_iff]
    simp
  · have habs : |t| = t := abs_of_pos hgt
    rw [habs] at ht
    have hle := h₁ t hgt (ht.trans (min_le_left _ _))
    refine hle.trans (le_of_eq ?_)
    rw [EReal.coe_eq_coe_iff, habs]
    ring

/-- **Sufficiency, quantitatively**: two-sided directional derivatives along a *basis* already
force the tangent affine estimate

```
f z ≤ f x + ⟨z - x, y₀⟩ + ε ‖z - x‖
```

on a ball whose radius depends only on `ε`.

Finite-dimensionality enters through a *cross-polytope* decomposition rather than through
compactness of the unit sphere, which keeps the argument quantitative. Writing `z - x = ∑ ξ j • b j`
and `S = ∑ |ξ j|`, the point `z` is the convex combination with weights `|ξ j| / S` of the points
`x + (S * sign (ξ j)) • b j`, each at distance `S` from `x` along a basis direction, where the
one-sided estimate applies. The linear terms recombine into `⟨z - x, y₀⟩` exactly and the error is
`S * η`, at most `ε ‖z - x‖` once `η` is scaled by the constant relating `∑ |ξ j|` to `‖z - x‖`. -/
theorem exists_le_of_forall_basis_dirDeriv_eq [FiniteDimensional ℝ E] (b : Module.Basis ι ℝ E)
    (hf : ConvexFn f) {r : ℝ} (hr : f x = (r : EReal)) {y₀ : StrongDual ℝ E}
    (hpos : ∀ j, dirDeriv f x (b j) = ((y₀ (b j) : ℝ) : EReal))
    (hneg : ∀ j, dirDeriv f x (-(b j)) = ((-(y₀ (b j)) : ℝ) : EReal))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : E, ‖z - x‖ ≤ δ →
      f z ≤ ((r + y₀ (z - x) + ε * ‖z - x‖ : ℝ) : EReal) := by
  classical
  obtain ⟨hι⟩ := nonempty_fintype ι
  obtain ⟨K, hK, hcoord⟩ : ∃ K : ℝ, 0 < K ∧ ∀ w : E, ∑ j, |b.repr w j| ≤ K * ‖w‖ := by
    set T : E →L[ℝ] (ι → ℝ) := LinearMap.toContinuousLinearMap (b.equivFun : E →ₗ[ℝ] (ι → ℝ))
      with hT
    refine ⟨(Fintype.card ι : ℝ) * ‖T‖ + 1, by positivity, fun w => ?_⟩
    have hbound : ∀ j : ι, |b.repr w j| ≤ ‖T‖ * ‖w‖ := by
      intro j
      have hTj : T w j = b.repr w j := by rw [hT]; simp [Module.Basis.equivFun_apply]
      have h1 : |b.repr w j| ≤ ‖T w‖ := by
        rw [← hTj]
        simpa using norm_le_pi_norm (T w) j
      exact h1.trans (T.le_opNorm w)
    calc ∑ j, |b.repr w j| ≤ ∑ _j : ι, ‖T‖ * ‖w‖ := Finset.sum_le_sum fun j _ => hbound j
      _ = (Fintype.card ι : ℝ) * (‖T‖ * ‖w‖) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      _ ≤ ((Fintype.card ι : ℝ) * ‖T‖ + 1) * ‖w‖ := by nlinarith [norm_nonneg w]
  set η : ℝ := ε / K with hηdef
  have hη : 0 < η := div_pos hε hK
  have hstep : ∀ j : ι, ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ t : ℝ, |t| ≤ a₀ →
      f (x + t • b j) ≤ ((r + t * y₀ (b j) + |t| * η : ℝ) : EReal) := fun j =>
    exists_forall_abs_le_of_dirDeriv_eq hf hr hη (hpos j) (hneg j)
  choose A hA hA' using hstep
  obtain ⟨c, hc, hcA⟩ : ∃ c : ℝ, 0 < c ∧ ∀ j, c ≤ A j := by
    rcases isEmpty_or_nonempty ι with hι | hι
    · exact ⟨1, one_pos, fun j => (IsEmpty.false j).elim⟩
    · obtain ⟨j₀, -, hj₀⟩ := Finset.exists_min_image (Finset.univ : Finset ι) A
        ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
      exact ⟨A j₀, hA j₀, fun j => hj₀ j (Finset.mem_univ j)⟩
  refine ⟨c / K, div_pos hc hK, fun z hz => ?_⟩
  set w : E := z - x with hwdef
  set ξ : ι → ℝ := fun j => b.repr w j with hξdef
  have hrepr : ∑ j, ξ j • b j = w := by
    simp [hξdef]
  have hy₀w : ∑ j, ξ j * y₀ (b j) = y₀ w := by
    rw [← hrepr, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul]
  set S : ℝ := ∑ j, |ξ j| with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hSK : S ≤ K * ‖w‖ := hcoord w
  have hSc : S ≤ c := by
    refine hSK.trans ?_
    have hle : K * ‖w‖ ≤ K * (c / K) := mul_le_mul_of_nonneg_left hz hK.le
    rwa [mul_div_cancel₀ c hK.ne'] at hle
  rcases hS0.eq_or_lt with hS | hSpos
  · have hzero : ∀ j, ξ j = 0 := by
      intro j
      have h := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => abs_nonneg (ξ j)).1 hS.symm j
        (Finset.mem_univ j)
      exact abs_eq_zero.1 h
    have hw0 : w = 0 := by rw [← hrepr]; simp [hzero]
    have hzx : z = x := by
      rw [hwdef] at hw0
      exact sub_eq_zero.1 hw0
    rw [hzx, hw0, hr]
    simp
  · set σ : ι → ℝ := fun j => if 0 ≤ ξ j then 1 else -1 with hσdef
    have habs : ∀ j, |S * σ j| = S := by
      intro j
      rw [abs_mul, abs_of_pos hSpos, hσdef]
      by_cases hj : 0 ≤ ξ j <;> simp [hj]
    have hmul : ∀ j, |ξ j| * σ j = ξ j := by
      intro j
      rw [hσdef]
      by_cases hj : 0 ≤ ξ j
      · simp [hj, abs_of_nonneg hj]
      · simp [hj, abs_of_neg (not_le.1 hj)]
    have hcoef : ∀ j : ι, (|ξ j| / S) * (S * σ j) = ξ j := by
      intro j
      have h : (|ξ j| / S) * (S * σ j) = (|ξ j| * σ j) * (S / S) := by ring
      rw [h, div_self hSpos.ne', mul_one, hmul j]
    have hw1 : ∑ j, |ξ j| / S = 1 := by
      rw [← Finset.sum_div, ← hSdef]
      exact div_self hSpos.ne'
    have hmem : ∀ j ∈ (Finset.univ : Finset ι),
        f (x + (S * σ j) • b j) ≤ ((r + (S * σ j) * y₀ (b j) + S * η : ℝ) : EReal) := by
      intro j _
      have h := hA' j (S * σ j) (by rw [habs j]; exact hSc.trans (hcA j))
      rwa [habs j] at h
    have hjensen : f (∑ j, (|ξ j| / S) • (x + (S * σ j) • b j)) ≤
        ((∑ j, (|ξ j| / S) * (r + (S * σ j) * y₀ (b j) + S * η) : ℝ) : EReal) :=
      hf.sum_le _ _ _ _ hmem (fun j _ => div_nonneg (abs_nonneg _) hSpos.le) hw1
    have hpt : ∑ j, (|ξ j| / S) • (x + (S * σ j) • b j) = z := by
      have hterm : ∀ j : ι,
          (|ξ j| / S) • (x + (S * σ j) • b j) = (|ξ j| / S) • x + ξ j • b j := by
        intro j
        rw [smul_add, smul_smul, hcoef j]
      calc ∑ j, (|ξ j| / S) • (x + (S * σ j) • b j)
          = ∑ j, ((|ξ j| / S) • x + ξ j • b j) := Finset.sum_congr rfl fun j _ => hterm j
        _ = (∑ j, |ξ j| / S) • x + ∑ j, ξ j • b j := by
            rw [Finset.sum_add_distrib, ← Finset.sum_smul]
        _ = x + w := by rw [hw1, one_smul, hrepr]
        _ = z := by rw [hwdef]; abel
    have hval : ∑ j, (|ξ j| / S) * (r + (S * σ j) * y₀ (b j) + S * η) = r + y₀ w + S * η := by
      have hterm : ∀ j : ι, (|ξ j| / S) * (r + (S * σ j) * y₀ (b j) + S * η)
          = (|ξ j| / S) * r + ξ j * y₀ (b j) + (|ξ j| / S) * (S * η) := by
        intro j
        have h : (|ξ j| / S) * (r + (S * σ j) * y₀ (b j) + S * η)
            = (|ξ j| / S) * r + ((|ξ j| / S) * (S * σ j)) * y₀ (b j) + (|ξ j| / S) * (S * η) := by
          ring
        rw [h, hcoef j]
      calc ∑ j, (|ξ j| / S) * (r + (S * σ j) * y₀ (b j) + S * η)
          = ∑ j, ((|ξ j| / S) * r + ξ j * y₀ (b j) + (|ξ j| / S) * (S * η)) :=
            Finset.sum_congr rfl fun j _ => hterm j
        _ = (∑ j, |ξ j| / S) * r + (∑ j, ξ j * y₀ (b j)) + (∑ j, |ξ j| / S) * (S * η) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
        _ = r + y₀ w + S * η := by rw [hw1, one_mul, one_mul, hy₀w]
    rw [hpt, hval] at hjensen
    refine hjensen.trans ?_
    rw [EReal.coe_le_coe_iff]
    have hSη : S * η ≤ ε * ‖w‖ := by
      calc S * η ≤ (K * ‖w‖) * η := mul_le_mul_of_nonneg_right hSK hη.le
        _ = ε * ‖w‖ := by rw [hηdef]; field_simp
    linarith

/-- The estimate of `exists_le_of_forall_basis_dirDeriv_eq` recovers `f'(x; ·)` in *every*
direction, not only along the basis: it bounds `f'(x; v)` above by `⟨v, y₀⟩`, and the general
inequality `-f'(x; -v) ≤ f'(x; v)` supplies the matching lower bound. This turns `n` two-sided
partial derivatives into linearity of `f'(x; ·)` without a detour that would need `f'(x; ·)` to be
proper first. -/
theorem dirDeriv_eq_of_forall_basis_dirDeriv_eq [FiniteDimensional ℝ E]
    (b : Module.Basis ι ℝ E) (hf : ConvexFn f) (ht : f x ≠ ⊤) (hb : f x ≠ ⊥)
    {y₀ : StrongDual ℝ E} (hpos : ∀ j, dirDeriv f x (b j) = ((y₀ (b j) : ℝ) : EReal))
    (hneg : ∀ j, dirDeriv f x (-(b j)) = ((-(y₀ (b j)) : ℝ) : EReal)) (v : E) :
    dirDeriv f x v = ((y₀ v : ℝ) : EReal) := by
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hb (lt_top_iff_ne_top.2 ht)
  have hle : ∀ u : E, dirDeriv f x u ≤ ((y₀ u : ℝ) : EReal) := by
    intro u
    rcases eq_or_ne u 0 with rfl | hu
    · rw [dirDeriv_zero ht hb]
      simp
    have hnu : 0 < ‖u‖ := norm_pos_iff.2 hu
    have hnu' : ‖u‖ ≠ 0 := hnu.ne'
    by_contra hcon
    obtain ⟨m, hm₁, hm₂⟩ := EReal.lt_iff_exists_real_btwn.1 (not_le.1 hcon)
    have hm' : y₀ u < m := by exact_mod_cast hm₁
    obtain ⟨δ, hδ, hup⟩ := exists_le_of_forall_basis_dirDeriv_eq b hf hr hpos hneg
      (div_pos (sub_pos.2 hm') hnu)
    set a : ℝ := min (δ / ‖u‖) 1 with hadef
    have ha : 0 < a := lt_min (div_pos hδ hnu) one_pos
    have hnorm : ‖x + a • u - x‖ ≤ δ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
      calc a * ‖u‖ ≤ (δ / ‖u‖) * ‖u‖ := mul_le_mul_of_nonneg_right (min_le_left _ _) hnu.le
        _ = δ := div_mul_cancel₀ δ hnu'
    have hbound := hup (x + a • u) hnorm
    rw [add_sub_cancel_left] at hbound
    have hfinal : dirDeriv f x u ≤ (m : EReal) := by
      refine (dirDeriv_le f x u ha).trans ?_
      rw [hr, EReal.sub_div_le_coe_iff ha]
      refine hbound.trans (le_of_eq ?_)
      rw [EReal.coe_eq_coe_iff, map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs,
        abs_of_pos ha]
      field_simp
      ring
    exact absurd hfinal (not_le.2 hm₂)
  refine le_antisymm (hle v) ?_
  have hneg' := hle (-v)
  rw [map_neg] at hneg'
  have h2 := EReal.neg_le_neg_iff.2 hneg'
  rw [← EReal.coe_neg, neg_neg] at h2
  exact h2.trans (neg_dirDeriv_neg_le hf ht hb v)

/-- **Sufficiency**, from two-sided derivatives along a basis: `f` is Fréchet differentiable at
`x`, with gradient the functional `y₀` whose values along the basis are the given
one-sided derivatives. The two-sided estimate `f x + ⟨z - x, y₀⟩ ≤ f z ≤ f x + ⟨z - x, y₀⟩ +
ε ‖z - x‖` does all three jobs at once: it makes `f` finite near `x`, so that the local real
representative exists, and exhibits the little-o estimate defining `HasFDerivAt`. -/
theorem hasGradientAtFn_of_forall_basis_dirDeriv_eq [FiniteDimensional ℝ E]
    (b : Module.Basis ι ℝ E) (hf : ConvexFn f) (ht : f x ≠ ⊤) (hb : f x ≠ ⊥)
    {y₀ : StrongDual ℝ E} (hpos : ∀ j, dirDeriv f x (b j) = ((y₀ (b j) : ℝ) : EReal))
    (hneg : ∀ j, dirDeriv f x (-(b j)) = ((-(y₀ (b j)) : ℝ) : EReal)) :
    HasGradientAtFn f y₀ x := by
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hb (lt_top_iff_ne_top.2 ht)
  have hall := dirDeriv_eq_of_forall_basis_dirDeriv_eq b hf ht hb hpos hneg
  have hsubg : y₀ ∈ subdifferential (topDualPairing ℝ E).flip f x :=
    (mem_subdifferential_iff_le_dirDeriv ht hb).2 fun v => le_of_eq (hall v).symm
  have hlow : ∀ z : E, ((r + y₀ (z - x) : ℝ) : EReal) ≤ f z := by
    intro z
    have h := hsubg z
    rwa [hr, show ((topDualPairing ℝ E).flip (z - x)) y₀ = y₀ (z - x) from rfl,
      ← EReal.coe_add] at h
  obtain ⟨δ₁, hδ₁, hup₁⟩ := exists_le_of_forall_basis_dirDeriv_eq b hf hr hpos hneg one_pos
  have hfin : ∀ z : E, ‖z - x‖ ≤ δ₁ → f z = (((f z).toReal : ℝ) : EReal) := by
    intro z hz
    refine (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _)
      (hup₁ z hz)) ?_).symm
    intro hbot
    have h := hlow z
    rw [hbot, le_bot_iff] at h
    exact absurd h (EReal.coe_ne_bot _)
  have hfg : f =ᶠ[𝓝 x] fun z => (((f z).toReal : ℝ) : EReal) := by
    filter_upwards [Metric.closedBall_mem_nhds x hδ₁] with z hz
    exact hfin z (by rwa [Metric.mem_closedBall, dist_eq_norm] at hz)
  have hgx : (f x).toReal = r := by rw [hr, EReal.toReal_coe]
  refine ⟨fun z => (f z).toReal, hfg, ?_⟩
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, hup⟩ := exists_le_of_forall_basis_dirDeriv_eq b hf hr hpos hneg hε
  filter_upwards [Metric.closedBall_mem_nhds x (lt_min hδ hδ₁)] with z hz
  have hzn : ‖z - x‖ ≤ min δ δ₁ := by rwa [Metric.mem_closedBall, dist_eq_norm] at hz
  have h1 := hup z (hzn.trans (min_le_left _ _))
  have h2 := hlow z
  rw [hfin z (hzn.trans (min_le_right _ _)), EReal.coe_le_coe_iff] at h1 h2
  rw [hgx, Real.norm_eq_abs, abs_le]
  exact ⟨by linarith, by linarith⟩

/-- **Sufficiency**: if the directional derivative `f'(x; ·)` is the linear function `⟨·, y₀⟩`,
then `f` is differentiable at `x` with `∇f x = y₀`. This is the previous theorem read at any basis;
the hypothesis in every direction is more than the proof consumes. -/
theorem hasGradientAtFn_of_dirDeriv_eq [FiniteDimensional ℝ E] (hf : ConvexFn f) (ht : f x ≠ ⊤)
    (hb : f x ≠ ⊥) {y₀ : StrongDual ℝ E}
    (h : ∀ v : E, dirDeriv f x v = ((y₀ v : ℝ) : EReal)) : HasGradientAtFn f y₀ x :=
  hasGradientAtFn_of_forall_basis_dirDeriv_eq (Module.finBasis ℝ E) hf ht hb (fun j => h _)
    (fun j => by rw [h, map_neg])

/-- **In full**: for a convex function finite at `x`, differentiability at `x` is equivalent to
linearity of `f'(x; ·)`. Necessity is `HasGradientAtFn.dirDeriv_eq` and sufficiency is
`hasGradientAtFn_of_dirDeriv_eq`. -/
theorem differentiableAtFn_iff_exists_dirDeriv_eq [FiniteDimensional ℝ E] (hf : ConvexFn f)
    (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) :
    DifferentiableAtFn f x ↔
      ∃ y₀ : StrongDual ℝ E, ∀ v : E, dirDeriv f x v = ((y₀ v : ℝ) : EReal) := by
  constructor
  · rintro ⟨y₀, hy₀⟩
    exact ⟨y₀, hy₀.dirDeriv_eq hf⟩
  · rintro ⟨y₀, h⟩
    exact ⟨y₀, hasGradientAtFn_of_dirDeriv_eq hf ht hb h⟩

/-- It is already enough that the `n` two-sided partial derivatives exist and are finite. Here
"the `n` partial derivatives" is the pair of one-sided derivatives along the vectors of a basis,
and "two-sided and finite" is the requirement that they be the negatives of each other and real.
The gradient is then `b.constr` of those numbers. -/
theorem differentiableAtFn_of_forall_basis_dirDeriv_eq [FiniteDimensional ℝ E]
    (b : Module.Basis ι ℝ E) (hf : ConvexFn f) (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) (c : ι → ℝ)
    (hpos : ∀ j, dirDeriv f x (b j) = ((c j : ℝ) : EReal))
    (hneg : ∀ j, dirDeriv f x (-(b j)) = ((-(c j) : ℝ) : EReal)) :
    DifferentiableAtFn f x := by
  refine ⟨LinearMap.toContinuousLinearMap (b.constr ℝ c), ?_⟩
  have hval : ∀ j, (LinearMap.toContinuousLinearMap (b.constr ℝ c)) (b j) = c j := fun j => by
    simp
  exact hasGradientAtFn_of_forall_basis_dirDeriv_eq b hf ht hb (fun j => by rw [hpos j, hval j])
    (fun j => by rw [hneg j, hval j])

end Sufficiency

end Frechet


/-! ### Exposed points of a half-cylinder -/

section HalfCylinder

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]

/-- The exposed points of a half-cylinder `C ×ˢ [0, ∞)` are the points `(z, 0)` with `z` an
exposed point of `C`. A functional exposing a point of the cylinder must be *strictly* decreasing
in the vertical direction, since otherwise the whole vertical ray attains the maximum; that forces
the height to be `0` and reduces the functional to one on `C`. The cylinder is the epigraph of an
indicator function, so this is how a statement about `epi f*` becomes one about a convex set. -/
theorem mem_exposedPoints_prod_Ici_iff {C : Set X} {z : X} {ν : ℝ} :
    (z, ν) ∈ (C ×ˢ Ici (0 : ℝ)).exposedPoints ℝ ↔ ν = 0 ∧ z ∈ C.exposedPoints ℝ := by
  constructor
  · rintro ⟨⟨hzC, hν⟩, L, hL⟩
    have hν0' : (0 : ℝ) ≤ ν := hν
    set c : ℝ := L (0, 1) with hcdef
    have hsplit : ∀ (w : X) (γ : ℝ), L (w, γ) = L (w, 0) + γ * c := by
      intro w γ
      have h1 : ((w, γ) : X × ℝ) = (w, 0) + (0, γ) := by
        rw [Prod.mk_add_mk, add_zero, zero_add]
      have h2 : ((0, γ) : X × ℝ) = γ • ((0 : X), (1 : ℝ)) := by
        rw [Prod.smul_mk, smul_zero, smul_eq_mul, mul_one]
      rw [h1, map_add, h2, map_smul, smul_eq_mul, ← hcdef, mul_comm]
    have hmemup : ((z, ν + 1) : X × ℝ) ∈ C ×ˢ Ici (0 : ℝ) := ⟨hzC, by simp; linarith⟩
    have hcneg : c < 0 := by
      have hle : c ≤ 0 := by
        have h := (hL _ hmemup).1
        rw [hsplit z (ν + 1), hsplit z ν] at h
        nlinarith
      refine lt_of_le_of_ne hle fun h0 => ?_
      have h := (hL _ hmemup).2 (by rw [hsplit z (ν + 1), hsplit z ν, h0]; simp)
      have : ν + 1 = ν := congrArg Prod.snd h
      linarith
    have hν0 : ν = 0 := by
      have h := (hL ((z, (0 : ℝ)) : X × ℝ) ⟨hzC, (mem_Ici.2 le_rfl)⟩).1
      rw [hsplit z 0, hsplit z ν] at h
      nlinarith
    subst hν0
    refine ⟨rfl, hzC, L.comp (ContinuousLinearMap.inl ℝ X ℝ), fun w hw => ⟨?_, fun hge => ?_⟩⟩
    · have h := (hL ((w, (0 : ℝ)) : X × ℝ) ⟨hw, (mem_Ici.2 le_rfl)⟩).1
      simpa using h
    · refine congrArg Prod.fst ((hL ((w, (0 : ℝ)) : X × ℝ) ⟨hw, (mem_Ici.2 le_rfl)⟩).2 ?_)
      simpa using hge
  · rintro ⟨rfl, hzC, l, hl⟩
    refine ⟨⟨hzC, (mem_Ici.2 le_rfl)⟩,
      l.comp (ContinuousLinearMap.fst ℝ X ℝ) - ContinuousLinearMap.snd ℝ X ℝ, ?_⟩
    have hval : ∀ (u : X) (δ : ℝ),
        (l.comp (ContinuousLinearMap.fst ℝ X ℝ) - ContinuousLinearMap.snd ℝ X ℝ) (u, δ)
          = l u - δ := by
      intro u δ
      simp
    rintro ⟨w, γ⟩ ⟨hw, hγ⟩
    have hγ0 : (0 : ℝ) ≤ γ := hγ
    obtain ⟨h1, h2⟩ := hl w hw
    refine ⟨by rw [hval, hval]; linarith, fun hge => ?_⟩
    rw [hval, hval] at hge
    have hγz : γ = 0 := le_antisymm (by linarith) hγ0
    have hwz : w = z := h2 (by linarith)
    rw [hwz, hγz]

end HalfCylinder

/-! ### Exposed points of the epigraph of a conjugate -/

section Exposed

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal}

/-- A subgradient pins down the value: if `y ∈ ∂f x` and `f* y = μ` is finite, then
`f x = ⟨x, y⟩ - μ`. This is Fenchel's equality solved for `f x`, and in particular `f x` is
finite. -/
theorem Proper.eq_sub_of_mem_subdifferential (hp : Proper f) {x : E} {y : F} {μ : ℝ}
    (hy : y ∈ subdifferential B f x) (hμ : conj B f y = (μ : EReal)) :
    f x = ((B x y - μ : ℝ) : EReal) := by
  have hfx : f x + conj B f y = ((B x y : ℝ) : EReal) :=
    hp.mem_subdifferential_iff_add_conj_eq.1 hy
  rw [hμ] at hfx
  have hxb : f x ≠ ⊥ := hp.ne_bot x
  have hxt : f x ≠ ⊤ := by
    intro h
    rw [h, EReal.top_add_of_ne_bot (EReal.coe_ne_bot μ)] at hfx
    exact absurd hfx (EReal.top_ne_coe _)
  have hxc : f x = (((f x).toReal : ℝ) : EReal) := (EReal.coe_toReal hxt hxb).symm
  rw [hxc, ← EReal.coe_add, EReal.coe_eq_coe_iff] at hfx
  rw [hxc, EReal.coe_eq_coe_iff]
  linarith

section Topology

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [TopologicalSpace F]

/-- In subgradient form: `(y, μ)` is an exposed point of `epi f*` exactly when `μ = f* y` and `y`
is the *only* subgradient of `f` at some point `x`.

Geometrically, a supporting hyperplane to `epi f*` touching it in a single point is necessarily
non-vertical, hence the graph of an affine function `⟨x, ·⟩ - α`; supporting `epi f*` at `(y, μ)`
says `x ∈ ∂f*(y)`, i.e. `y ∈ ∂f x`, and touching nowhere else says `∂f x` is no larger than `{y}`.
Only the forward direction uses closedness, through `∂f* = (∂f)⁻¹`. -/
theorem mem_exposedPoints_epi_conj_iff [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (hf : ConvexFn f) (hp : Proper f) (hc : ClosedFn f) {y : F} {μ : ℝ} :
    (y, μ) ∈ (epi (conj B f)).exposedPoints ℝ ↔
      conj B f y = (μ : EReal) ∧ ∃ x : E, subdifferential B f x = {y} := by
  have hbot : ∀ z : F, conj B f z ≠ ⊥ := conj_ne_bot hp.dom_nonempty
  constructor
  · rintro ⟨hmem, L, hL⟩
    have hmem' : conj B f y ≤ (μ : EReal) := hmem
    -- Split `L` into a functional on `F` and a coefficient of the vertical direction.
    obtain ⟨x₀, hx₀⟩ := exists_pairing_eq B.flip (L.comp (ContinuousLinearMap.inl ℝ F ℝ))
    set c : ℝ := L (0, 1) with hcdef
    have hsplit : ∀ (z : F) (β : ℝ), L (z, β) = B x₀ z + β * c := by
      intro z β
      have h1 : ((z, β) : F × ℝ) = (z, 0) + (0, β) := by
        rw [Prod.mk_add_mk, add_zero, zero_add]
      have h2 : ((0, β) : F × ℝ) = β • ((0 : F), (1 : ℝ)) := by
        rw [Prod.smul_mk, smul_zero, smul_eq_mul, mul_one]
      have h3 : L (z, 0) = B x₀ z := by
        simpa [LinearMap.flip_apply] using hx₀ z
      rw [h1, map_add, h3, h2, map_smul, smul_eq_mul, ← hcdef, mul_comm]
    -- The vertical direction is a direction of recession of the epigraph.
    have hup : ∀ t : ℝ, 0 ≤ t → (y, μ + t) ∈ epi (conj B f) := fun t ht =>
      hmem'.trans (by exact_mod_cast le_add_of_nonneg_right ht)
    have hcneg : c < 0 := by
      have hle : c ≤ 0 := by
        have h := (hL _ (hup 1 zero_le_one)).1
        rw [hsplit, hsplit] at h
        nlinarith
      refine lt_of_le_of_ne hle fun h0 => ?_
      have heq : L (y, μ) ≤ L (y, μ + 1) := by rw [hsplit, hsplit, h0]; simp
      have := (hL _ (hup 1 zero_le_one)).2 heq
      have hμ' : μ + 1 = μ := congrArg Prod.snd this
      linarith
    -- Normalise the functional so that the vertical coefficient is `-1`.
    have hcne : c ≠ 0 := ne_of_lt hcneg
    have hpos : (0 : ℝ) < (-c)⁻¹ := inv_pos.2 (neg_pos.2 hcneg)
    set x : E := (-c)⁻¹ • x₀ with hxdef
    have hBx : ∀ z : F, B x z = (-c)⁻¹ * B x₀ z := by
      intro z
      rw [hxdef, map_smul, LinearMap.smul_apply, smul_eq_mul]
    have hmax : ∀ (z : F) (β : ℝ), conj B f z ≤ (β : EReal) → B x z - β ≤ B x y - μ := by
      intro z β hzβ
      have h := (hL (z, β) hzβ).1
      rw [hsplit, hsplit] at h
      have h' : (-c)⁻¹ * (B x₀ z + β * c) ≤ (-c)⁻¹ * (B x₀ y + μ * c) :=
        mul_le_mul_of_nonneg_left h hpos.le
      have e1 : (-c)⁻¹ * (β * c) = -β := by field_simp
      have e2 : (-c)⁻¹ * (μ * c) = -μ := by field_simp
      rw [mul_add, mul_add, e1, e2] at h'
      rw [hBx, hBx]
      linarith
    have huniq : ∀ (z : F) (β : ℝ), conj B f z ≤ (β : EReal) →
        B x y - μ ≤ B x z - β → (z, β) = (y, μ) := by
      intro z β hzβ hge
      refine (hL (z, β) hzβ).2 ?_
      rw [hBx, hBx] at hge
      have h' : (-c) * ((-c)⁻¹ * B x₀ y - μ) ≤ (-c) * ((-c)⁻¹ * B x₀ z - β) :=
        mul_le_mul_of_nonneg_left hge (neg_nonneg.2 hcneg.le)
      have e1 : (-c) * ((-c)⁻¹ * B x₀ y) = B x₀ y := by field_simp
      have e2 : (-c) * ((-c)⁻¹ * B x₀ z) = B x₀ z := by field_simp
      rw [mul_sub, mul_sub, e1, e2] at h'
      rw [hsplit, hsplit]
      nlinarith
    -- The value at `y` is `μ`.
    have hyt : conj B f y ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top μ) hmem'
    have hyc : conj B f y = (((conj B f y).toReal : ℝ) : EReal) :=
      (EReal.coe_toReal hyt (hbot y)).symm
    have hνμ : (conj B f y).toReal ≤ μ := by
      rw [hyc, EReal.coe_le_coe_iff] at hmem'
      exact hmem'
    have hμν : μ ≤ (conj B f y).toReal := by
      have := hmax y _ (le_of_eq hyc)
      linarith
    have hμeq : conj B f y = (μ : EReal) := by
      rw [hyc, EReal.coe_eq_coe_iff]
      linarith
    -- `y` is a subgradient at `x`, and the only one.
    have hysub : y ∈ subdifferential B f x := by
      rw [← mem_subdifferential_conj_iff_of_closedFn hf hc, mem_subdifferential_iff_forall_sub_le]
      intro z
      rcases eq_or_ne (conj B f z) ⊤ with hz | hz
      · rw [hz]
        simp
      · have hzc : conj B f z = (((conj B f z).toReal : ℝ) : EReal) :=
          (EReal.coe_toReal hz (hbot z)).symm
        have h := hmax z _ (le_of_eq hzc)
        rw [LinearMap.flip_apply, LinearMap.flip_apply, hzc, hμeq, ← EReal.coe_sub,
          ← EReal.coe_sub, EReal.coe_le_coe_iff]
        exact h
    refine ⟨hμeq, x, Set.eq_singleton_iff_unique_mem.2 ⟨hysub, fun z hz => ?_⟩⟩
    have hfx : f x = ((B x y - μ : ℝ) : EReal) := hp.eq_sub_of_mem_subdifferential hysub hμeq
    have hzc : conj B f z = ((B x z : ℝ) : EReal) - f x := mem_subdifferential_iff_conj_eq.1 hz
    rw [hfx, ← EReal.coe_sub] at hzc
    have := huniq z (B x z - (B x y - μ)) (le_of_eq hzc) (by simp)
    exact congrArg Prod.fst this
  · rintro ⟨hμ, x, hx⟩
    have hy : y ∈ subdifferential B f x := by rw [hx]; rfl
    have hfx : f x = ((B x y - μ : ℝ) : EReal) := hp.eq_sub_of_mem_subdifferential hy hμ
    refine ⟨le_of_eq hμ, (evalCLM B.flip x).comp (ContinuousLinearMap.fst ℝ F ℝ) -
      ContinuousLinearMap.snd ℝ F ℝ, ?_⟩
    have hval : ∀ (w : F) (γ : ℝ),
        ((evalCLM B.flip x).comp (ContinuousLinearMap.fst ℝ F ℝ) -
          ContinuousLinearMap.snd ℝ F ℝ) (w, γ) = B x w - γ := by
      intro w γ
      simp [LinearMap.flip_apply]
    rintro ⟨z, β⟩ hzβ
    have hzβ' : conj B f z ≤ (β : EReal) := hzβ
    have hzt : conj B f z ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top β) hzβ'
    have hzc : conj B f z = (((conj B f z).toReal : ℝ) : EReal) :=
      (EReal.coe_toReal hzt (hbot z)).symm
    have hrβ : (conj B f z).toReal ≤ β := by
      rw [hzc, EReal.coe_le_coe_iff] at hzβ'
      exact hzβ'
    have hfen := hp.le_add_conj (B := B) x z
    rw [hfx, hzc, ← EReal.coe_add, EReal.coe_le_coe_iff] at hfen
    refine ⟨?_, fun hge => ?_⟩
    · rw [hval, hval]
      linarith
    · rw [hval, hval] at hge
      have hβr : β = (conj B f z).toReal := by linarith
      have hzsub : z ∈ subdifferential B f x := by
        refine mem_subdifferential_iff_conj_eq.2 ?_
        rw [hzc, hfx, ← EReal.coe_sub, EReal.coe_eq_coe_iff]
        linarith
      have hzy : z = y := by rw [hx] at hzsub; exact hzsub
      subst hzy
      rw [hμ, EReal.toReal_coe] at hβr
      rw [hβr]

/-! ### Exposed points of a set cut out by a positively homogeneous function -/

section Homogeneous

variable [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] in
/-- The exposed points of a set are the values of the subdifferential of any positively
homogeneous function that cuts it out. If `g` is closed proper convex and positively
homogeneous and `C = {x | ⟨x, y⟩ ≤ g y for all y}` — for instance `g` the support function of
`C` — then `z` is an exposed point of `C` exactly when `z` is the *only* subgradient of `g` at some
`y`. The conjugate of `g` is the indicator of `C`, so `epi g*` is the half-cylinder `C ×ˢ [0, ∞)`
and this is the previous result read at height `0`. -/
theorem mem_exposedPoints_supportSet_iff [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    {g : F → EReal} (hgh : PosHomogeneous g) (hgc : ConvexFn g) (hgp : Proper g)
    (hgcl : ClosedFn g) {z : E} :
    z ∈ (supportSet B.flip g).exposedPoints ℝ ↔ ∃ y : F, subdifferential B.flip g y = {z} := by
  have hne : ∃ w, g w ≠ ⊤ := by
    obtain ⟨w, hw⟩ := hgp.dom_nonempty
    exact ⟨w, hw.ne⟩
  have hind : conj B.flip g = indicatorFn (supportSet B.flip g) :=
    conj_eq_indicatorFn_of_posHomogeneous hgh hne
  have hepi : epi (conj B.flip g) = supportSet B.flip g ×ˢ Ici (0 : ℝ) := by
    rw [hind, epi_indicatorFn]
  constructor
  · intro hz
    have h1 : ((z, (0 : ℝ)) : E × ℝ) ∈ (epi (conj B.flip g)).exposedPoints ℝ := by
      rw [hepi]
      exact mem_exposedPoints_prod_Ici_iff.2 ⟨rfl, hz⟩
    exact ((mem_exposedPoints_epi_conj_iff (B := B.flip) hgc hgp hgcl).1 h1).2
  · rintro ⟨y, hy⟩
    have hzsub : z ∈ subdifferential B.flip g y := by rw [hy]; rfl
    have hzt : conj B.flip g z ≠ ⊤ := by
      intro htop
      have heq := hgp.mem_subdifferential_iff_add_conj_eq.1 hzsub
      rw [htop, add_comm, EReal.top_add_of_ne_bot (hgp.ne_bot y)] at heq
      exact absurd heq (EReal.top_ne_coe _)
    have hzC : z ∈ supportSet B.flip g := by
      by_contra hzn
      rw [hind, indicatorFn_of_notMem hzn] at hzt
      exact hzt rfl
    have hz0 : conj B.flip g z = ((0 : ℝ) : EReal) := by
      rw [hind, indicatorFn_of_mem hzC, EReal.coe_zero]
    have h1 := (mem_exposedPoints_epi_conj_iff (B := B.flip) hgc hgp hgcl
      (y := z) (μ := (0 : ℝ))).2 ⟨hz0, y, hy⟩
    rw [hepi] at h1
    exact (mem_exposedPoints_prod_Ici_iff.1 h1).2

end Homogeneous

end Topology

end Exposed

end ConvexAnalysis
