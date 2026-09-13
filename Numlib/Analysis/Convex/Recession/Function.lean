import Numlib.Analysis.Convex.Closure
import Numlib.Analysis.Convex.Homogenize
import Numlib.Analysis.Convex.Recession.Cone

/-!
# Recession functions

The *recession function* `f0⁺` of `f : E → EReal` has as its epigraph the recession cone of the
epigraph of `f`: `epi (f0⁺) = 0⁺(epi f)` (`epi_recessionFn`, for every `f`). It says how fast `f`
can grow in each direction: `(f0⁺) y ≤ ν` means `f (x + a • y) ≤ f x + a * ν` for all `x`, `a ≥ 0`.
The directions with `(f0⁺) y ≤ 0` form the *recession cone of `f`*, those with `(f0⁺) (±y) ≤ 0`
its *constancy space*, and those with `(f0⁺) (-y) = -(f0⁺) y` its *lineality space*.

Most of the theory needs only a real vector space with no topology; closedness of `epi f` enters
exactly where the answer must not depend on the base point `x`, and is always carried as
`IsClosed (epi f)`, never as `ClosedFn f`, which also collapses improper functions to `⊥`.

## Main definitions

* `recessionFn f` — the recession function `f0⁺`, as `ofEpi (0⁺(epi f))`.
* `recessionConeFn f`, `recessionPointedConeFn f` — the recession cone, bare and as a `PointedCone`.
* `constancySpace f`, `constancySubmodule f` — the constancy space, bare and as a `Submodule ℝ E`.
* `linealitySpaceFn f`, `linealitySubmoduleFn f`, `linealityFn f` — the lineality space of `f`
  and its dimension.

## Main results

* `posHomogeneous_recessionFn`, `convexFn_recessionFn`, `proper_recessionFn` — `f0⁺` is positively
  homogeneous and convex, proper when `f` is proper and closed when `f` is closed; and
  `recessionFn_apply_eq_iSup_sub`: `(f0⁺) y = sup {f (x + y) - f x | x ∈ dom f}`, reached for
  closed `f` by the difference quotients at any one `x ∈ dom f` (Theorem 8.5 in [^1]).
* `recessionFn_isLeast` — `f0⁺` is the least `h` with `f z ≤ f x + h (z - x)`.
* `tendsto_smulRight_recessionFn` — `(f0⁺) y = lim_{a ↓ 0} (fa) y`.
* `antitone_along_of_liminf_lt_top`, `forall_antitone_iff_recessionFn_nonpos` — a convex `f` that
  does not blow up along one half-line is nonincreasing along the whole line, and `(f0⁺) y ≤ 0`
  says exactly that this happens from every base point; `ConvexFn.eq_of_le_on_affineSubspace` is
  the affine-set form.
* `recessionCone_setOf_le`, `linealitySpace_setOf_le` — all nonempty level sets of a closed convex
  `f` share its recession cone and constancy space, and by `isBounded_setOf_le` one of them is
  bounded only if all are.
* `forall_eq_add_iff_mk_mem_linealitySpace_epi`, `linealitySpaceFn_eq_image` —
  `f` is affine with slope `ν` along `y` exactly when `(y, ν)` lies in the lineality space of
  `epi f`, whose projection is the lineality space of `f`.

## References

[^1]: R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §8.
-/

open Filter Pointwise Set Topology

namespace ConvexAnalysis

/-! ### The recession function -/

section Defs

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {f g : E → EReal} {x y : E} {ν : ℝ}

/-- The **recession function** `f0⁺` of `f`: the function whose epigraph is the recession cone of
the epigraph of `f`. It is *defined* as `ofEpi` of that cone, which is all one can write down
before knowing the cone is an epigraph; `epi_recessionFn` then proves `epi (f0⁺) = 0⁺(epi f)`. -/
noncomputable def recessionFn (f : E → EReal) : E → EReal := ofEpi (recessionCone (epi f))

/-- The recession condition on `(y, ν)`, unfolded against the epigraph: `(y, ν)` recedes from
`epi f` exactly when `f (x + a • y) ≤ μ + a * ν` whenever `f x ≤ μ` and `a ≥ 0`. -/
theorem mk_mem_recessionCone_epi :
    ((y, ν) : E × ℝ) ∈ recessionCone (epi f) ↔
      ∀ (x : E) (μ : ℝ), f x ≤ (μ : EReal) →
        ∀ a : ℝ, 0 ≤ a → f (x + a • y) ≤ ((μ + a * ν : ℝ) : EReal) := by
  constructor
  · intro h x μ hx a ha
    simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using h (x, μ) (mk_mem_epi.2 hx) a ha
  · rintro h ⟨x, μ⟩ hp a ha
    simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using h x μ (mk_mem_epi.1 hp) a ha

/-- The recession condition on `(y, ν)`, in `EReal` arithmetic: `f (x + a • y) ≤ f x + a * ν` for
every `x` and every `a ≥ 0`. Equivalent to the epigraph form even at improper values, because
`⊥ + (r : ℝ) = ⊥` matches "`f x ≤ μ` for every real `μ`". -/
theorem mk_mem_recessionCone_epi_iff :
    ((y, ν) : E × ℝ) ∈ recessionCone (epi f) ↔
      ∀ (x : E) (a : ℝ), 0 ≤ a → f (x + a • y) ≤ f x + ((a * ν : ℝ) : EReal) := by
  rw [mk_mem_recessionCone_epi]
  constructor
  · intro h x a ha
    rcases eq_top_or_lt_top (f x) with hx | hx
    · rw [hx, _root_.EReal.top_add_of_ne_bot (_root_.EReal.coe_ne_bot _)]
      exact le_top
    by_cases hb : f x = ⊥
    · rw [hb, _root_.EReal.bot_add, le_bot_iff]
      refine EReal.eq_bot_of_forall_le_coe fun s => ?_
      simpa using h x (s - a * ν) (hb ▸ bot_le) a ha
    · obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hb hx
      rw [hr, ← _root_.EReal.coe_add]
      exact h x r hr.le a ha
  · intro h x μ hx a ha
    rw [_root_.EReal.coe_add]
    exact (h x a ha).trans (add_le_add hx le_rfl)

/-- A vertical section of `0⁺(epi f)` is upward closed: this is one of the two halves of
`IsEpiLike`. -/
theorem mk_mem_recessionCone_epi_of_le (h : ((y, ν) : E × ℝ) ∈ recessionCone (epi f)) {ρ : ℝ}
    (hνρ : ν ≤ ρ) : ((y, ρ) : E × ℝ) ∈ recessionCone (epi f) := by
  rw [mk_mem_recessionCone_epi] at h ⊢
  intro x μ hx a ha
  refine (h x μ hx a ha).trans ?_
  have hstep : μ + a * ν ≤ μ + a * ρ := by nlinarith
  exact_mod_cast hstep

/-- **The recession cone of an epigraph is an epigraph**, with no hypothesis on `f` whatsoever.

Vertical sections are upward closed because `μ + a * ν` grows with `ν`, and they are closed from
below because `f (x + a • y) ≤ μ + a * ρ` for every `ρ > ν` forces `f (x + a • y) ≤ μ + a * ν`.
Neither half needs `epi f` to be closed or convex. -/
theorem isEpiLike_recessionCone_epi (f : E → EReal) : IsEpiLike (recessionCone (epi f)) := by
  refine isEpiLike_of_forall (fun _ _ _ hμ hμν => mk_mem_recessionCone_epi_of_le hμ hμν)
    fun y ν h => ?_
  rw [mk_mem_recessionCone_epi]
  intro x μ hx a ha
  refine EReal.le_coe_of_forall_lt fun q hq => ?_
  rcases ha.eq_or_lt with rfl | ha'
  · simp only [zero_smul, add_zero, zero_mul] at hq ⊢
    exact lt_of_le_of_lt hx (by exact_mod_cast hq)
  · have hd : 0 < (q - (μ + a * ν)) / (2 * a) := div_pos (by linarith) (by linarith)
    have hle := mk_mem_recessionCone_epi.1 (h (ν + (q - (μ + a * ν)) / (2 * a)) (by linarith))
      x μ hx a ha
    refine lt_of_le_of_lt hle ?_
    have heq : μ + a * (ν + (q - (μ + a * ν)) / (2 * a)) = μ + a * ν + (q - (μ + a * ν)) / 2 := by
      field_simp
      ring
    rw [heq]
    exact_mod_cast (by linarith : μ + a * ν + (q - (μ + a * ν)) / 2 < q)

/-- **The defining property of the recession function**: its epigraph is the recession cone of the
epigraph. Rockafellar takes this as the definition; here it is a theorem, and it carries no
hypothesis on `f`. -/
@[simp]
theorem epi_recessionFn (f : E → EReal) : epi (recessionFn f) = recessionCone (epi f) :=
  epi_ofEpi (isEpiLike_recessionCone_epi f)

/-- The `≤`-characterisation of `f0⁺` against a real bound, in epigraph form. -/
theorem recessionFn_le_coe_iff :
    recessionFn f y ≤ (ν : EReal) ↔ ((y, ν) : E × ℝ) ∈ recessionCone (epi f) := by
  rw [← epi_recessionFn]
  exact mk_mem_epi.symm

/-- The `≤`-characterisation of `f0⁺` against an arbitrary function: `f0⁺` is the greatest function
whose epigraph contains `0⁺(epi f)`. -/
theorem le_recessionFn_iff : g ≤ recessionFn f ↔ recessionCone (epi f) ⊆ epi g :=
  subset_epi_iff_le_ofEpi.symm

/-- The pointwise `≤`-characterisation in `EReal` arithmetic. -/
theorem recessionFn_le_coe_iff_forall :
    recessionFn f y ≤ (ν : EReal) ↔
      ∀ (x : E) (a : ℝ), 0 ≤ a → f (x + a • y) ≤ f x + ((a * ν : ℝ) : EReal) := by
  rw [recessionFn_le_coe_iff, mk_mem_recessionCone_epi_iff]

/-- For a *convex* `f` it is enough to test the recession inequality at `a = 1`: a convex set
recedes in a direction as soon as it is stable under one step in it. -/
theorem recessionFn_le_coe_iff_of_convexFn (hf : ConvexFn f) :
    recessionFn f y ≤ (ν : EReal) ↔ ∀ x : E, f (x + y) ≤ f x + (ν : EReal) := by
  rw [recessionFn_le_coe_iff, mem_recessionCone_iff_forall_add_mem hf.convex_epi]
  constructor
  · intro h x
    rcases eq_top_or_lt_top (f x) with hx | hx
    · rw [hx, _root_.EReal.top_add_of_ne_bot (_root_.EReal.coe_ne_bot _)]
      exact le_top
    by_cases hb : f x = ⊥
    · rw [hb, _root_.EReal.bot_add, le_bot_iff]
      refine EReal.eq_bot_of_forall_le_coe fun s => ?_
      have hmem := h (x, s - ν) (mk_mem_epi.2 (hb ▸ bot_le))
      rw [Prod.mk_add_mk] at hmem
      simpa using mk_mem_epi.1 hmem
    · obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hb hx
      have hmem := h (x, r) (mk_mem_epi.2 hr.le)
      rw [Prod.mk_add_mk] at hmem
      rw [hr, ← _root_.EReal.coe_add]
      exact mk_mem_epi.1 hmem
  · rintro h ⟨x, μ⟩ hp
    rw [Prod.mk_add_mk]
    refine mk_mem_epi.2 ?_
    rw [_root_.EReal.coe_add]
    exact (h x).trans (add_le_add (mk_mem_epi.1 hp) le_rfl)

/-! ### `f0⁺` is a positively homogeneous convex function -/

/-- A positive multiple of a recession cone is that recession cone: `0⁺C` is a cone. This is the
scaling half of `recessionPointedCone`, in the `a • s = s` form that
`posHomogeneous_iff_isCone_epi` asks for. -/
theorem smul_recessionCone {a : ℝ} (ha : 0 < a) (C : Set E) :
    a • recessionCone C = recessionCone C := by
  refine Set.Subset.antisymm ?_ fun z hz => ?_
  · rintro _ ⟨w, hw, rfl⟩
    exact smul_mem_recessionCone ha.le hw
  · exact ⟨a⁻¹ • z, smul_mem_recessionCone (by positivity) hz, smul_inv_smul₀ ha.ne' z⟩

/-- **The recession function is positively homogeneous.** No hypothesis on `f` is needed, because
`0⁺(epi f)` is a cone for every `f`. -/
theorem posHomogeneous_recessionFn (f : E → EReal) : PosHomogeneous (recessionFn f) := by
  rw [posHomogeneous_iff_isCone_epi]
  intro a ha
  rw [epi_recessionFn]
  exact smul_recessionCone ha (epi f)

/-- **The recession function is convex.** Again no hypothesis on `f` is needed: `0⁺C` is convex
for every `C`, convex or not. -/
theorem convexFn_recessionFn (f : E → EReal) : ConvexFn (recessionFn f) :=
  convexFn_iff_convex_epi.2 (by rw [epi_recessionFn]; exact convex_recessionCone (epi f))

/-- `epi (f0⁺)` bundled as a cone. The two theorems above would give it as a `ConvexCone ℝ (E × ℝ)`
via `PosHomogeneous.epiCone`, but `recessionPointedCone` already carries the same set as a
`PointedCone ℝ (E × ℝ)`, with no hypothesis, so that is the bundling recorded here. -/
@[simp]
theorem coe_recessionPointedCone_epi (f : E → EReal) :
    (recessionPointedCone (epi f) : Set (E × ℝ)) = epi (recessionFn f) := by
  rw [coe_recessionPointedCone, epi_recessionFn]

/-- `f0⁺` is nonpositive at the origin, because `0` recedes from every set. -/
theorem recessionFn_apply_zero_le (f : E → EReal) : recessionFn f 0 ≤ 0 := by
  have h : ((0 : E), (0 : ℝ)) ∈ recessionCone (epi f) := by
    rw [Prod.mk_zero_zero]
    exact zero_mem_recessionCone (epi f)
  simpa using recessionFn_le_coe_iff.2 h

/-- `f0⁺` never takes the value `-∞` when `f` is proper.

Properness is needed on both counts: for `f ≡ +∞` the epigraph is empty, `0⁺∅` is everything and
`f0⁺ ≡ -∞`; and if `f` takes the value `-∞` somewhere, a vertical section of `0⁺(epi f)` can be
all of `ℝ`. -/
theorem recessionFn_ne_bot (hp : Proper f) (y : E) : recessionFn f y ≠ ⊥ := by
  intro hbot
  obtain ⟨x, hx⟩ := hp.dom_nonempty
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot x) hx
  refine hp.ne_bot (x + y) (EReal.eq_bot_of_forall_le_coe fun s => ?_)
  have hmem : ((y, s - r) : E × ℝ) ∈ recessionCone (epi f) :=
    recessionFn_le_coe_iff.1 (hbot ▸ bot_le)
  have hle := mk_mem_recessionCone_epi.1 hmem x r hr.le 1 zero_le_one
  simpa using hle

@[simp]
theorem recessionFn_apply_zero (hp : Proper f) : recessionFn f 0 = 0 := by
  refine le_antisymm (recessionFn_apply_zero_le f) (EReal.le_of_forall_coe_le fun r hr => ?_)
  obtain ⟨x, hx⟩ := hp.dom_nonempty
  obtain ⟨s, hs⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot x) hx
  have hle := mk_mem_recessionCone_epi.1 (recessionFn_le_coe_iff.1 hr) x s hs.le 1 zero_le_one
  rw [smul_zero, add_zero, hs] at hle
  have hss : s ≤ s + 1 * r := by exact_mod_cast hle
  exact_mod_cast (by linarith : (0 : ℝ) ≤ r)

/-- The recession function of a proper convex function is proper. -/
theorem proper_recessionFn (hp : Proper f) : Proper (recessionFn f) where
  dom_nonempty := ⟨0, by rw [mem_dom, recessionFn_apply_zero hp]; exact _root_.EReal.zero_lt_top⟩
  ne_bot := recessionFn_ne_bot hp

/-! ### The difference formula and the least-function property -/

omit [Module ℝ E] in
/-- Rearranging `f (x + y) ≤ f x + r` as a difference quotient. The `⊥`-freeness hypothesis is
what makes `f x` real on `dom f`, and the restriction to `dom f` is what keeps `⊤ + r = ⊤` from
being read as a constraint. -/
theorem forall_le_add_coe_iff (hbot : ∀ x, f x ≠ ⊥) {r : ℝ} :
    (∀ x : E, f (x + y) ≤ f x + (r : EReal)) ↔ ∀ x ∈ dom f, f (x + y) - f x ≤ (r : EReal) := by
  constructor
  · intro h x hx
    obtain ⟨s, hs⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hbot x) hx
    rw [hs, _root_.EReal.sub_le_iff_le_add (Or.inl (_root_.EReal.coe_ne_bot s))
      (Or.inl (_root_.EReal.coe_ne_top s)), add_comm ((r : ℝ) : EReal) ((s : ℝ) : EReal), ← hs]
    exact h x
  · intro h x
    rcases eq_top_or_lt_top (f x) with hx | hx
    · rw [hx, _root_.EReal.top_add_of_ne_bot (_root_.EReal.coe_ne_bot _)]
      exact le_top
    · obtain ⟨s, hs⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hbot x) hx
      have hstep := h x hx
      rw [hs] at hstep ⊢
      rwa [_root_.EReal.sub_le_iff_le_add (Or.inl (_root_.EReal.coe_ne_bot s))
        (Or.inl (_root_.EReal.coe_ne_top s)),
        add_comm ((r : ℝ) : EReal) ((s : ℝ) : EReal)] at hstep

/-- **The difference formula**

`(f0⁺) y = sup {f (x + y) - f x | x ∈ dom f}`.

Convexity enters by letting the recession condition be tested at `a = 1` only, and
`∀ x, f x ≠ ⊥` is what makes the difference meaningful. Properness is *not* needed: for
`f ≡ +∞` both sides are `-∞`, the supremum because `dom f = ∅`. -/
theorem recessionFn_apply_eq_iSup_sub (hf : ConvexFn f) (hbot : ∀ x, f x ≠ ⊥) (y : E) :
    recessionFn f y = ⨆ x ∈ dom f, (f (x + y) - f x) := by
  refine EReal.eq_of_forall_le_coe_iff fun r => ?_
  rw [recessionFn_le_coe_iff_of_convexFn hf, forall_le_add_coe_iff hbot, iSup₂_le_iff]

/-- The inequality `f (x + y) ≤ f x + (f0⁺) y`: `f0⁺` is one such bounding function. -/
theorem le_add_recessionFn (hf : ConvexFn f) (hp : Proper f) (x y : E) :
    f (x + y) ≤ f x + recessionFn f y := by
  rcases eq_top_or_lt_top (f x) with hx | hx
  · rw [hx, _root_.EReal.top_add_of_ne_bot (recessionFn_ne_bot hp y)]
    exact le_top
  obtain ⟨s, hs⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot x) hx
  have hterm : f (x + y) - f x ≤ recessionFn f y := by
    rw [recessionFn_apply_eq_iSup_sub hf hp.ne_bot]
    exact le_iSup₂ (f := fun x' (_ : x' ∈ dom f) => f (x' + y) - f x') x hx
  calc f (x + y) = f (x + y) - f x + f x := by rw [hs]; exact _root_.EReal.sub_add_cancel.symm
    _ ≤ recessionFn f y + f x := add_le_add hterm le_rfl
    _ = f x + recessionFn f y := add_comm _ _

/-- `f0⁺` is the *least* function `h` for which `f` satisfies the global inequality
`f z ≤ f x + h (z - x)` at every pair of points. -/
theorem recessionFn_isLeast (hf : ConvexFn f) (hp : Proper f) :
    IsLeast {h : E → EReal | ∀ x z : E, f z ≤ f x + h (z - x)} (recessionFn f) := by
  refine ⟨fun x z => ?_, fun h hh y => ?_⟩
  · have hxz : x + (z - x) = z := by abel
    have hle := le_add_recessionFn hf hp x (z - x)
    rwa [hxz] at hle
  · rw [recessionFn_apply_eq_iSup_sub hf hp.ne_bot]
    refine iSup₂_le fun x hx => ?_
    obtain ⟨s, hs⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot x) hx
    have hstep := hh x (x + y)
    rw [add_sub_cancel_left, hs, add_comm ((s : ℝ) : EReal) (h y)] at hstep
    rw [hs]
    exact (_root_.EReal.sub_le_iff_le_add (Or.inl (_root_.EReal.coe_ne_bot s))
      (Or.inl (_root_.EReal.coe_ne_top s))).2 hstep

/-! ### Directions of recession -/

/-- The recession inequality at `ν = 0`: `(f0⁺) y ≤ 0` means that moving in the direction `y`
never increases `f`. -/
theorem add_smul_le_of_recessionFn_nonpos (h : recessionFn f y ≤ 0) (x : E) {a : ℝ} (ha : 0 ≤ a) :
    f (x + a • y) ≤ f x := by
  have h0 : recessionFn f y ≤ ((0 : ℝ) : EReal) := by rwa [_root_.EReal.coe_zero]
  simpa using recessionFn_le_coe_iff_forall.1 h0 x a ha

theorem recessionFn_nonpos_iff :
    recessionFn f y ≤ 0 ↔ ∀ (x : E) (a : ℝ), 0 ≤ a → f (x + a • y) ≤ f x := by
  refine ⟨fun h x a ha => add_smul_le_of_recessionFn_nonpos h x ha, fun h => ?_⟩
  have h0 : recessionFn f y ≤ ((0 : ℝ) : EReal) :=
    recessionFn_le_coe_iff_forall.2 fun x a ha => by simpa using h x a ha
  rwa [_root_.EReal.coe_zero] at h0

/-- **`f (x + a • y)` is a nonincreasing function of `a` for *every* `x` exactly when
`(f0⁺) y ≤ 0`.**

This half needs no hypothesis on `f` at all, neither convexity nor properness; the usual
statement carries "proper convex" because it is packaged with the two implications below. -/
theorem forall_antitone_iff_recessionFn_nonpos :
    (∀ x : E, Antitone fun a : ℝ => f (x + a • y)) ↔ recessionFn f y ≤ 0 := by
  rw [recessionFn_nonpos_iff]
  constructor
  · intro h x a ha
    have hstep := h x ha
    simpa using hstep
  · intro h x a₁ a₂ h12
    have hcoef : a₁ + (a₂ - a₁) = a₂ := by ring
    have hstep := h (x + a₁ • y) (a₂ - a₁) (by linarith)
    rwa [add_assoc, ← add_smul, hcoef] at hstep

/-- **A convex function that fails to blow up along one half-line is nonincreasing along the whole
line**: a finite `liminf` of `f (x + a • y)` as `a → ∞` makes `a ↦ f (x + a • y)` antitone.

The proof is elementary, and in particular needs no closure, no relative interiors and no finite
dimension: for `λ₁ < λ₂` and a real bound `μ` on `f (x + λ₁ • y)`, write `x + λ₂ • y` as a convex
combination of `x + λ₁ • y` and `x + λ • y` for a very large `λ` with `f (x + λ • y) < α`; the
weight on the second point tends to `0`, so convexity gives `f (x + λ₂ • y) ≤ μ` in the limit. -/
theorem antitone_along_of_liminf_lt_top (hf : ConvexFn f) (x y : E)
    (h : liminf (fun a : ℝ => f (x + a • y)) atTop < ⊤) :
    Antitone fun a : ℝ => f (x + a • y) := by
  obtain ⟨α, hα, -⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 h
  have hfreq : ∃ᶠ a : ℝ in atTop, f (x + a • y) < (α : EReal) :=
    frequently_lt_of_liminf_lt (h := hα)
  intro a₁ a₂ h12
  refine EReal.le_of_forall_coe_le fun μ hμ => ?_
  refine EReal.le_coe_of_forall_lt fun q hq => ?_
  rcases h12.eq_or_lt with rfl | hlt
  · exact lt_of_le_of_lt hμ (by exact_mod_cast hq)
  have hc0 : (0 : ℝ) < |α - μ| + 1 := by positivity
  have hp0 : (0 : ℝ) < q - μ := by linarith
  obtain ⟨l, hlα, hlB⟩ := (hfreq.and_eventually (eventually_ge_atTop
    (max (a₂ + 1) (a₁ + (a₂ - a₁) * (|α - μ| + 1) / (q - μ))))).exists
  have hl2 : a₂ + 1 ≤ l := le_trans (le_max_left _ _) hlB
  have hl1 : a₁ + (a₂ - a₁) * (|α - μ| + 1) / (q - μ) ≤ l := le_trans (le_max_right _ _) hlB
  have hlpos : (0 : ℝ) < l - a₁ := by linarith
  have ht0 : (0 : ℝ) < (a₂ - a₁) / (l - a₁) := div_pos (by linarith) hlpos
  have ht1 : (a₂ - a₁) / (l - a₁) < 1 := (div_lt_one hlpos).2 (by linarith)
  have hmul : (a₂ - a₁) / (l - a₁) * (l - a₁) = a₂ - a₁ := div_mul_cancel₀ _ hlpos.ne'
  have htc : (a₂ - a₁) / (l - a₁) * (|α - μ| + 1) ≤ q - μ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hlpos]
    have hstep := (div_le_iff₀ hp0).1
      (by linarith : (a₂ - a₁) * (|α - μ| + 1) / (q - μ) ≤ l - a₁)
    linarith
  have hpt : (1 - (a₂ - a₁) / (l - a₁)) * μ + (a₂ - a₁) / (l - a₁) * α < q := by
    have hlt' : α - μ < |α - μ| + 1 := by linarith [le_abs_self (α - μ)]
    have h1 : (a₂ - a₁) / (l - a₁) * (α - μ) < (a₂ - a₁) / (l - a₁) * (|α - μ| + 1) :=
      mul_lt_mul_of_pos_left hlt' ht0
    have hex : (1 - (a₂ - a₁) / (l - a₁)) * μ + (a₂ - a₁) / (l - a₁) * α
        = μ + (a₂ - a₁) / (l - a₁) * (α - μ) := by ring
    rw [hex]
    linarith
  have hcombo := hf.epi_combo hμ hlα.le (by linarith : (0 : ℝ) ≤ 1 - (a₂ - a₁) / (l - a₁))
    ht0.le (by ring)
  have harg : (1 - (a₂ - a₁) / (l - a₁)) • (x + a₁ • y)
      + ((a₂ - a₁) / (l - a₁)) • (x + l • y) = x + a₂ • y := by
    have hcoef : (1 - (a₂ - a₁) / (l - a₁)) * a₁ + (a₂ - a₁) / (l - a₁) * l = a₂ := by
      have hex : (1 - (a₂ - a₁) / (l - a₁)) * a₁ + (a₂ - a₁) / (l - a₁) * l
          = a₁ + (a₂ - a₁) / (l - a₁) * (l - a₁) := by ring
      rw [hex, hmul]
      ring
    rw [smul_add, smul_add, smul_smul, smul_smul, add_add_add_comm, ← add_smul, ← add_smul,
      show (1 : ℝ) - (a₂ - a₁) / (l - a₁) + (a₂ - a₁) / (l - a₁) = 1 by ring, one_smul, hcoef]
  rw [harg] at hcombo
  exact lt_of_le_of_lt hcombo (by exact_mod_cast hpt)

/-- `f` is constant along every line in the direction `y` exactly when both `(f0⁺) y ≤ 0` and
`(f0⁺) (-y) ≤ 0`. -/
theorem forall_eq_iff_recessionFn_nonpos :
    (∀ (x : E) (a : ℝ), f (x + a • y) = f x) ↔
      recessionFn f y ≤ 0 ∧ recessionFn f (-y) ≤ 0 := by
  constructor
  · intro h
    refine ⟨recessionFn_nonpos_iff.2 fun x a _ => (h x a).le,
      recessionFn_nonpos_iff.2 fun x a _ => ?_⟩
    rw [smul_neg, ← neg_smul]
    exact (h x (-a)).le
  · rintro ⟨h1, h2⟩
    have h2' : ∀ (x : E) (a : ℝ), 0 ≤ a → f (x - a • y) ≤ f x := by
      intro x a ha
      have := recessionFn_nonpos_iff.1 h2 x a ha
      rwa [smul_neg, ← sub_eq_add_neg] at this
    intro x a
    rcases le_or_gt 0 a with ha | ha
    · refine le_antisymm (recessionFn_nonpos_iff.1 h1 x a ha) ?_
      have := h2' (x + a • y) a ha
      rwa [add_sub_cancel_right] at this
    · have hna : 0 ≤ -a := by linarith
      refine le_antisymm ?_ ?_
      · have := h2' x (-a) hna
        rwa [neg_smul, sub_neg_eq_add] at this
      · have := recessionFn_nonpos_iff.1 h1 (x + a • y) (-a) hna
        rwa [add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero] at this

/-- Along a single line: a convex function bounded above on a whole line is constant on it. -/
theorem ConvexFn.eq_of_forall_le_along_line (hf : ConvexFn f) {x z : E} {α : ℝ}
    (h : ∀ a : ℝ, f (x + a • (z - x)) ≤ (α : EReal)) : f z = f x := by
  have key : ∀ (u v : E), (∀ a : ℝ, f (u + a • (v - u)) ≤ (α : EReal)) → f v ≤ f u := by
    intro u v hu
    have hlim : liminf (fun a : ℝ => f (u + a • (v - u))) atTop ≤ (α : EReal) :=
      liminf_le_of_frequently_le' (Frequently.of_forall hu)
    have hanti := antitone_along_of_liminf_lt_top hf u (v - u)
      (lt_of_le_of_lt hlim (_root_.EReal.coe_lt_top α))
    have hstep := hanti (zero_le_one' ℝ)
    simpa using hstep
  have hzx : ∀ a : ℝ, f (z + a • (x - z)) ≤ (α : EReal) := by
    intro a
    have harg : z + a • (x - z) = x + (1 - a) • (z - x) := by
      rw [sub_smul, one_smul, smul_sub, smul_sub]
      abel
    rw [harg]
    exact h (1 - a)
  exact le_antisymm (key x z h) (key z x hzx)

/-- **A convex function is constant on any affine set on which it is bounded above.**

It follows from the line version above, applied along the line through any two points of `M`, so
no closure and no relative interiors are needed. Finiteness of `f` on `M` is not needed either,
since the two inequalities hold whatever value `f` takes. -/
theorem ConvexFn.eq_of_le_on_affineSubspace (hf : ConvexFn f) {M : AffineSubspace ℝ E} {α : ℝ}
    (hM : ∀ w ∈ M, f w ≤ (α : EReal)) {x z : E} (hx : x ∈ M) (hz : z ∈ M) : f z = f x := by
  refine hf.eq_of_forall_le_along_line fun a => hM _ ?_
  have hmem := M.smul_vsub_vadd_mem a hz hx hx
  simpa [vsub_eq_sub, vadd_eq_add, add_comm] using hmem

/-! ### The recession cone, constancy space and lineality space of a function -/

/-- The **recession cone of `f`** — not to be confused with the recession cone of `epi f`. It is
the horizontal slice `{y | (y, 0) ∈ 0⁺(epi f)}` of the latter, and it collects the directions in
which `f` recedes. -/
def recessionConeFn (f : E → EReal) : Set E := {y | recessionFn f y ≤ 0}

@[simp]
theorem mem_recessionConeFn : y ∈ recessionConeFn f ↔ recessionFn f y ≤ 0 := Iff.rfl

/-- The recession cone of `f` is the horizontal slice of the recession cone of `epi f`. -/
theorem mem_recessionConeFn_iff_mk :
    y ∈ recessionConeFn f ↔ ((y, (0 : ℝ)) : E × ℝ) ∈ recessionCone (epi f) := by
  rw [mem_recessionConeFn, ← recessionFn_le_coe_iff, _root_.EReal.coe_zero]

/-- The recession cone of `f` is a convex cone containing the origin, bundled as a
`PointedCone ℝ E`. No hypothesis on `f` is needed. -/
def recessionPointedConeFn (f : E → EReal) : PointedCone ℝ E where
  carrier := recessionConeFn f
  zero_mem' := recessionFn_apply_zero_le f
  add_mem' {y z} hy hz := by
    have h := add_mem_recessionCone (mem_recessionConeFn_iff_mk.1 hy)
      (mem_recessionConeFn_iff_mk.1 hz)
    rw [Prod.mk_add_mk, add_zero] at h
    exact mem_recessionConeFn_iff_mk.2 h
  smul_mem' c y hy := by
    have h := smul_mem_recessionCone c.2 (mem_recessionConeFn_iff_mk.1 hy)
    rw [Prod.smul_mk, smul_eq_mul, mul_zero] at h
    exact mem_recessionConeFn_iff_mk.2 h

@[simp]
theorem coe_recessionPointedConeFn (f : E → EReal) :
    (recessionPointedConeFn f : Set E) = recessionConeFn f := rfl

@[simp]
theorem mem_recessionPointedConeFn : y ∈ recessionPointedConeFn f ↔ y ∈ recessionConeFn f :=
  Iff.rfl

theorem convex_recessionConeFn (f : E → EReal) : Convex ℝ (recessionConeFn f) :=
  ((recessionPointedConeFn f : ConvexCone ℝ E)).convex

/-- The **constancy space of `f`**: the largest subspace inside the recession cone of `f`, which
collects the directions in which `f` is constant. -/
def constancySpace (f : E → EReal) : Set E := recessionConeFn f ∩ (-recessionConeFn f)

theorem mem_constancySpace :
    y ∈ constancySpace f ↔ recessionFn f y ≤ 0 ∧ recessionFn f (-y) ≤ 0 := by
  simp [constancySpace]

/-- The constancy space is exactly the set of directions along which `f` is constant. -/
theorem mem_constancySpace_iff_forall_eq :
    y ∈ constancySpace f ↔ ∀ (x : E) (a : ℝ), f (x + a • y) = f x := by
  rw [mem_constancySpace, ← forall_eq_iff_recessionFn_nonpos]

/-- The constancy space is the lineality space of the recession cone of `f`, hence a subspace,
bundled as a `Submodule ℝ E`. -/
noncomputable def constancySubmodule (f : E → EReal) : Submodule ℝ E :=
  (recessionPointedConeFn f).lineal

@[simp]
theorem coe_constancySubmodule (f : E → EReal) :
    (constancySubmodule f : Set E) = constancySpace f := by
  ext z; simp [constancySubmodule, constancySpace]

@[simp]
theorem mem_constancySubmodule : y ∈ constancySubmodule f ↔ y ∈ constancySpace f := by
  rw [← SetLike.mem_coe, coe_constancySubmodule]

/-- The constancy space is the largest subspace inside the recession cone of `f`. -/
theorem constancySubmodule_isGreatest (f : E → EReal) :
    IsGreatest {L : Submodule ℝ E | (L : Set E) ⊆ recessionConeFn f} (constancySubmodule f) := by
  refine ⟨?_, fun L hL z hz => ?_⟩
  · intro z hz
    rw [SetLike.mem_coe, mem_constancySubmodule, mem_constancySpace] at hz
    exact hz.1
  · exact mem_constancySubmodule.2 (mem_constancySpace.2 ⟨hL hz, hL (L.neg_mem hz)⟩)

/-! ### Directions in which `f` is affine -/

/-- Two opposite directions of recession of a proper `f` have nonnegative total slope: adding the
two recession directions gives `(0, ν + ρ) ∈ 0⁺(epi f)`, and `(f0⁺) 0 = 0`. -/
theorem zero_le_add_of_recessionFn_le (hp : Proper f) {ν ρ : ℝ}
    (h1 : recessionFn f y ≤ (ν : EReal)) (h2 : recessionFn f (-y) ≤ (ρ : EReal)) : 0 ≤ ν + ρ := by
  have hsum := add_mem_recessionCone (recessionFn_le_coe_iff.1 h1) (recessionFn_le_coe_iff.1 h2)
  rw [Prod.mk_add_mk, add_neg_cancel] at hsum
  have hle : recessionFn f 0 ≤ ((ν + ρ : ℝ) : EReal) := recessionFn_le_coe_iff.2 hsum
  rw [recessionFn_apply_zero hp] at hle
  exact_mod_cast hle

/-- A bound on `(f0⁺) (-y)` is a *lower* bound on `(f0⁺) y`. -/
theorem le_recessionFn_of_neg_le (hp : Proper f) {ν : ℝ}
    (h : recessionFn f (-y) ≤ ((-ν : ℝ) : EReal)) : (ν : EReal) ≤ recessionFn f y :=
  EReal.le_of_forall_coe_le fun r hr => by
    have hsum := zero_le_add_of_recessionFn_le hp hr h
    exact_mod_cast (by linarith : ν ≤ r)

/-- `(y, ν)` lies in the lineality space of `epi f` exactly when `(f0⁺) y = ν` and
`(f0⁺) (-y) = -ν`. Properness is what upgrades the inequalities `(f0⁺) y ≤ ν`,
`(f0⁺) (-y) ≤ -ν` to equalities. -/
theorem mk_mem_linealitySpace_epi_iff (hp : Proper f) {ν : ℝ} :
    ((y, ν) : E × ℝ) ∈ linealitySpace (epi f) ↔
      recessionFn f y = (ν : EReal) ∧ recessionFn f (-y) = ((-ν : ℝ) : EReal) := by
  rw [mem_linealitySpace]
  constructor
  · rintro ⟨h1, h2⟩
    have h2' : ((-y, -ν) : E × ℝ) ∈ recessionCone (epi f) := h2
    have hle1 : recessionFn f y ≤ (ν : EReal) := recessionFn_le_coe_iff.2 h1
    have hle2 : recessionFn f (-y) ≤ ((-ν : ℝ) : EReal) := recessionFn_le_coe_iff.2 h2'
    refine ⟨le_antisymm hle1 (le_recessionFn_of_neg_le hp hle2), le_antisymm hle2 ?_⟩
    have hback : recessionFn f (-(-y)) ≤ ((-(-ν) : ℝ) : EReal) := by
      rw [neg_neg, neg_neg]
      exact hle1
    exact le_recessionFn_of_neg_le hp hback
  · rintro ⟨h1, h2⟩
    refine ⟨recessionFn_le_coe_iff.1 h1.le, ?_⟩
    exact (recessionFn_le_coe_iff.1 h2.le : ((-y, -ν) : E × ℝ) ∈ recessionCone (epi f))

/-- If `(y, ν)` lies in the lineality space of `epi f`, then `f (x + a • y) = f x + a * ν` on the
forward half-line `a ≥ 0`. -/
theorem eq_add_of_mk_mem_linealitySpace_epi (h : ((y, ν) : E × ℝ) ∈ linealitySpace (epi f))
    (x : E) {a : ℝ} (ha : 0 ≤ a) : f (x + a • y) = f x + ((a * ν : ℝ) : EReal) := by
  rw [mem_linealitySpace] at h
  obtain ⟨h1, h2⟩ := h
  have h2' : ((-y, -ν) : E × ℝ) ∈ recessionCone (epi f) := h2
  refine le_antisymm (mk_mem_recessionCone_epi_iff.1 h1 x a ha) ?_
  have hback := mk_mem_recessionCone_epi_iff.1 h2' (x + a • y) a ha
  rw [smul_neg, add_neg_cancel_right] at hback
  have hstep : f x + ((a * ν : ℝ) : EReal)
      ≤ f (x + a • y) + (((a * -ν : ℝ) : EReal) + ((a * ν : ℝ) : EReal)) := by
    rw [← add_assoc]
    exact add_le_add hback le_rfl
  rwa [← _root_.EReal.coe_add, show a * -ν + a * ν = 0 by ring, _root_.EReal.coe_zero,
    add_zero] at hstep

/-- `f` is affine with slope `ν` along the whole line through every `x` in the direction `y`
exactly when `(y, ν)` lies in the lineality space of `epi f`. No hypothesis on `f` is needed
for this half. -/
theorem forall_eq_add_iff_mk_mem_linealitySpace_epi :
    (∀ (x : E) (a : ℝ), f (x + a • y) = f x + ((a * ν : ℝ) : EReal)) ↔
      ((y, ν) : E × ℝ) ∈ linealitySpace (epi f) := by
  rw [mem_linealitySpace]
  constructor
  · intro h
    refine ⟨mk_mem_recessionCone_epi_iff.2 fun x a _ => (h x a).le, ?_⟩
    refine (mk_mem_recessionCone_epi_iff.2 fun x a _ => ?_ :
      ((-y, -ν) : E × ℝ) ∈ recessionCone (epi f))
    have hstep := h x (-a)
    rw [neg_smul, ← smul_neg, show -a * ν = a * -ν by ring] at hstep
    exact hstep.le
  · rintro ⟨h1, h2⟩
    have h2' : ((-y, -ν) : E × ℝ) ∈ recessionCone (epi f) := h2
    have hmem : ((y, ν) : E × ℝ) ∈ linealitySpace (epi f) := mem_linealitySpace.2 ⟨h1, h2⟩
    have hmem' : ((-y, -ν) : E × ℝ) ∈ linealitySpace (epi f) := by
      refine mem_linealitySpace.2 ⟨h2', ?_⟩
      have hnn : -((-y, -ν) : E × ℝ) = ((y, ν) : E × ℝ) := by
        rw [show ((-y, -ν) : E × ℝ) = -((y, ν) : E × ℝ) from rfl, neg_neg]
      rw [hnn]
      exact h1
    intro x a
    rcases le_or_gt 0 a with hpos | hneg
    · exact eq_add_of_mk_mem_linealitySpace_epi hmem x hpos
    · have hstep := eq_add_of_mk_mem_linealitySpace_epi hmem' x (a := -a) (by linarith)
      rwa [neg_smul_neg, show -a * -ν = a * ν by ring] at hstep

/-- For proper `f`, being affine along `y` with slope `ν` is `(f0⁺) y = ν` together with
`(f0⁺) (-y) = -ν`. -/
theorem forall_eq_add_iff_recessionFn (hp : Proper f) :
    (∀ (x : E) (a : ℝ), f (x + a • y) = f x + ((a * ν : ℝ) : EReal)) ↔
      recessionFn f y = (ν : EReal) ∧ recessionFn f (-y) = ((-ν : ℝ) : EReal) :=
  forall_eq_add_iff_mk_mem_linealitySpace_epi.trans (mk_mem_linealitySpace_epi_iff hp)

/-- The **lineality space of `f`**: the directions in which `f` is affine, that is the `y` with
`(f0⁺) (-y) = -(f0⁺) y`. -/
def linealitySpaceFn (f : E → EReal) : Set E := {y | recessionFn f (-y) = -recessionFn f y}

@[simp]
theorem mem_linealitySpaceFn :
    y ∈ linealitySpaceFn f ↔ recessionFn f (-y) = -recessionFn f y := Iff.rfl

/-- The lineality space of `f` is the image of the lineality space of `epi f` under the projection
`(y, ν) ↦ y`. -/
theorem linealitySpaceFn_eq_image (hp : Proper f) :
    linealitySpaceFn f = Prod.fst '' linealitySpace (epi f) := by
  ext z
  constructor
  · intro hz
    have hz' : recessionFn f (-z) = -recessionFn f z := hz
    have hne : recessionFn f z ≠ ⊤ := by
      intro hc
      rw [hc] at hz'
      exact recessionFn_ne_bot hp (-z) (by rwa [_root_.EReal.neg_top] at hz')
    obtain ⟨ν, hν⟩ :=
      EReal.exists_coe_of_ne_bot_of_lt_top (recessionFn_ne_bot hp z) (lt_top_iff_ne_top.2 hne)
    refine ⟨(z, ν), (mk_mem_linealitySpace_epi_iff hp).2 ⟨hν, ?_⟩, rfl⟩
    rw [hz', hν, ← _root_.EReal.coe_neg]
  · rintro ⟨⟨w, ν⟩, hw, rfl⟩
    obtain ⟨h1, h2⟩ := (mk_mem_linealitySpace_epi_iff hp).1 hw
    change recessionFn f (-w) = -recessionFn f w
    rw [h1, h2, _root_.EReal.coe_neg]

/-- The lineality space of `f` is a subspace, bundled as a `Submodule ℝ E`. It is defined as the
image of `linealitySubmodule (epi f)` under the projection, so the subspace structure is free, and
`coe_linealitySubmoduleFn` identifies its carrier with `linealitySpaceFn`. -/
noncomputable def linealitySubmoduleFn (f : E → EReal) : Submodule ℝ E :=
  Submodule.map (LinearMap.fst ℝ E ℝ) (linealitySubmodule (epi f))

/-- The carrier of `linealitySubmoduleFn` is the lineality space of `f`. -/
theorem coe_linealitySubmoduleFn (hp : Proper f) :
    (linealitySubmoduleFn f : Set E) = linealitySpaceFn f := by
  rw [linealitySpaceFn_eq_image hp, linealitySubmoduleFn, Submodule.map_coe,
    coe_linealitySubmodule]
  rfl

/-- The *lineality of `f`*: the dimension of its lineality space. -/
noncomputable def linealityFn (f : E → EReal) : ℕ := Module.finrank ℝ (linealitySubmoduleFn f)

/-- **An affine direction of recession along which `f` is bounded below is a direction of
constancy.** If `y` is a direction of recession of a proper `f` in which `f` is affine
(`y ∈ linealitySpaceFn f`) and `f` is bounded below on the half-line `x + a • y`, `a ≥ 0`, issuing
from some `x ∈ dom f`, then `y ∈ constancySpace f`. Affineness turns the hypotheses on `y` into
`f (x + a • y) = f x + a * ν` with `ν = (f0⁺) y ≤ 0`, and the lower bound forces `ν = 0`. -/
theorem mem_constancySpace_of_mem_linealitySpaceFn (hp : Proper f)
    (hy : y ∈ recessionConeFn f) (hlin : y ∈ linealitySpaceFn f) {x : E} (hx : x ∈ dom f)
    {β : ℝ} (hbdd : ∀ a : ℝ, 0 ≤ a → (β : EReal) ≤ f (x + a • y)) : y ∈ constancySpace f := by
  have hle : recessionFn f y ≤ 0 := hy
  obtain ⟨ν, hν⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (recessionFn_ne_bot hp y)
    (hle.trans_lt (by simp))
  have hνle : ν ≤ 0 := by exact_mod_cast hν ▸ hle
  have hneg : recessionFn f (-y) = ((-ν : ℝ) : EReal) := by
    rw [mem_linealitySpaceFn.1 hlin, hν, ← _root_.EReal.coe_neg]
  have haff := (forall_eq_add_iff_recessionFn hp).2 ⟨hν, hneg⟩
  obtain ⟨μ, hμ⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot x) hx
  have hkey : ∀ a : ℝ, 0 ≤ a → β ≤ μ + a * ν := by
    intro a ha
    have hval := hbdd a ha
    rw [haff x a, hμ, ← _root_.EReal.coe_add] at hval
    exact_mod_cast hval
  have hν0 : ν = 0 := by
    rcases lt_or_eq_of_le hνle with hlt | heq
    · exfalso
      have hb0 : β ≤ μ := by simpa using hkey 0 le_rfl
      have hpos : 0 < -ν := by linarith
      have hcancel : (μ - β + 1) / (-ν) * (-ν) = μ - β + 1 := div_mul_cancel₀ _ hpos.ne'
      have hstep := hkey ((μ - β + 1) / (-ν)) (by positivity)
      nlinarith
    · exact heq
  refine mem_constancySpace.2 ⟨?_, ?_⟩
  · rw [hν, hν0]; simp
  · rw [hneg, hν0]; simp

end Defs

/-! ### Difference quotients -/

section Quotient

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {f : E → EReal} {x y : E}

/-- The difference quotient `(f (x + a • y) - f x) / a` is below `ν` exactly when the point
`(x, f x) + a • (y, ν)` lies in `epi f`. This is the translation that turns the difference formula
into a statement about a single half-line. -/
theorem coe_inv_mul_sub_le_coe_iff (hbot : ∀ z, f z ≠ ⊥) (hx : x ∈ dom f) {a ν : ℝ} (ha : 0 < a) :
    ((a⁻¹ : ℝ) : EReal) * (f (x + a • y) - f x) ≤ (ν : EReal) ↔
      f (x + a • y) ≤ f x + ((a * ν : ℝ) : EReal) := by
  obtain ⟨s, hs⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hbot x) hx
  rw [hs]
  constructor
  · intro hle
    have h2 : ((a : ℝ) : EReal) * (((a⁻¹ : ℝ) : EReal) * (f (x + a • y) - (s : EReal)))
        ≤ ((a : ℝ) : EReal) * ((ν : ℝ) : EReal) :=
      mul_le_mul_of_nonneg_left hle (by exact_mod_cast ha.le)
    rw [← mul_assoc, EReal.coe_mul_coe, mul_inv_cancel₀ ha.ne', _root_.EReal.coe_one,
      one_mul, EReal.coe_mul_coe] at h2
    rw [add_comm ((s : ℝ) : EReal) ((a * ν : ℝ) : EReal)]
    exact (_root_.EReal.sub_le_iff_le_add (Or.inl (_root_.EReal.coe_ne_bot s))
      (Or.inl (_root_.EReal.coe_ne_top s))).1 h2
  · intro hle
    rw [add_comm ((s : ℝ) : EReal) ((a * ν : ℝ) : EReal)] at hle
    have h2 := (_root_.EReal.sub_le_iff_le_add (Or.inl (_root_.EReal.coe_ne_bot s))
      (Or.inl (_root_.EReal.coe_ne_top s))).2 hle
    have h3 : ((a⁻¹ : ℝ) : EReal) * (f (x + a • y) - (s : EReal))
        ≤ ((a⁻¹ : ℝ) : EReal) * ((a * ν : ℝ) : EReal) :=
      mul_le_mul_of_nonneg_left h2 (by exact_mod_cast (inv_pos.2 ha).le)
    rwa [EReal.coe_mul_coe, show a⁻¹ * (a * ν) = ν by field_simp] at h3

/-- **The difference quotient is nondecreasing** in `a`. Convexity is the whole content:
`x + a₁ • y` is a convex combination of `x` and `x + a₂ • y`. -/
theorem monotone_coe_inv_mul_sub (hf : ConvexFn f) (hbot : ∀ z, f z ≠ ⊥) (hx : x ∈ dom f) (y : E)
    {a₁ a₂ : ℝ} (h1 : 0 < a₁) (h12 : a₁ ≤ a₂) :
    ((a₁⁻¹ : ℝ) : EReal) * (f (x + a₁ • y) - f x)
      ≤ ((a₂⁻¹ : ℝ) : EReal) * (f (x + a₂ • y) - f x) := by
  have h2 : 0 < a₂ := lt_of_lt_of_le h1 h12
  obtain ⟨s, hs⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hbot x) hx
  refine EReal.le_of_forall_coe_le fun ν hν => ?_
  rw [coe_inv_mul_sub_le_coe_iff hbot hx h1]
  have hν' := (coe_inv_mul_sub_le_coe_iff hbot hx h2).1 hν
  rw [hs] at hν' ⊢
  have hmem2 : f (x + a₂ • y) ≤ ((s + a₂ * ν : ℝ) : EReal) := by
    rw [_root_.EReal.coe_add]
    exact hν'
  have hq0 : (0 : ℝ) ≤ a₁ / a₂ := div_nonneg h1.le h2.le
  have hq1 : a₁ / a₂ ≤ 1 := (div_le_one h2).2 h12
  have hcombo := hf.epi_combo hs.le hmem2 (by linarith : (0 : ℝ) ≤ 1 - a₁ / a₂) hq0 (by ring)
  have harg : (1 - a₁ / a₂) • x + (a₁ / a₂) • (x + a₂ • y) = x + a₁ • y := by
    rw [smul_add, smul_smul, ← add_assoc, ← add_smul,
      show (1 : ℝ) - a₁ / a₂ + a₁ / a₂ = 1 by ring, one_smul,
      show a₁ / a₂ * a₂ = a₁ by field_simp]
  have hval : (1 - a₁ / a₂) * s + a₁ / a₂ * (s + a₂ * ν) = s + a₁ * ν := by
    field_simp
    ring
  rwa [harg, hval, _root_.EReal.coe_add] at hcombo

end Quotient

/-! ### The recession function of an indicator -/

section Indicator

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {C : Set E}

/-- The recession cone of `C ×ˢ [0, ∞)` — that is, of `epi δ(· | C)` — is `0⁺C ×ˢ [0, ∞)`. -/
theorem recessionCone_prod_Ici (hC : C.Nonempty) :
    recessionCone (C ×ˢ Set.Ici (0 : ℝ)) = recessionCone C ×ˢ Set.Ici (0 : ℝ) := by
  obtain ⟨x₀, hx₀⟩ := hC
  ext ⟨y, ν⟩
  constructor
  · intro h
    refine ⟨fun x hx a ha => ?_, ?_⟩
    · simpa using (h (x, 0) ⟨hx, le_refl (0 : ℝ)⟩ a ha).1
    · have hstep := (h (x₀, 0) ⟨hx₀, le_refl (0 : ℝ)⟩ 1 zero_le_one).2
      have h2 : (0 : ℝ) ≤ 0 + 1 * ν := hstep
      change (0 : ℝ) ≤ ν
      linarith
  · rintro ⟨hy, hν⟩ ⟨x, μ⟩ ⟨hx, hμ⟩ a ha
    have hμ' : (0 : ℝ) ≤ μ := hμ
    have hν' : (0 : ℝ) ≤ ν := hν
    refine ⟨by simpa using hy x hx a ha, ?_⟩
    have : (0 : ℝ) ≤ μ + a * ν := by nlinarith
    simpa using this

/-- The recession function of an indicator function is the indicator function of the recession
cone. Nonemptiness of `C` is needed: for `C = ∅` the left-hand side is the constant `-∞`, since
`epi δ(· | ∅) = ∅` and `0⁺∅` is everything, while the right-hand side is the constant `0`. -/
theorem recessionFn_indicatorFn (hC : C.Nonempty) :
    recessionFn (indicatorFn C) = indicatorFn (recessionCone C) :=
  (eq_ofEpi_of_epi_eq (by
    rw [epi_indicatorFn, epi_indicatorFn, recessionCone_prod_Ici hC])).symm

/-- The recession *cone* of an indicator function is the recession cone of the set. -/
theorem recessionConeFn_indicatorFn (hC : C.Nonempty) :
    recessionConeFn (indicatorFn C) = recessionCone C := by
  ext y
  rw [mem_recessionConeFn, recessionFn_indicatorFn hC]
  by_cases hy : y ∈ recessionCone C
  · rw [indicatorFn_of_mem hy]
    simp [hy]
  · rw [indicatorFn_of_notMem hy]
    simp [hy]

end Indicator

/-! ### Closed functions: the limit formula, and testing at a single base point -/

section Topological

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] {f : E → EReal} {x y : E}

/-- `f0⁺` is closed as soon as `f` is. Only closedness of `epi f` is used; neither convexity nor
nonemptiness enters. -/
theorem isClosed_epi_recessionFn (hc : IsClosed (epi f)) : IsClosed (epi (recessionFn f)) := by
  rw [epi_recessionFn]
  exact isClosed_recessionCone hc

theorem lowerSemicontinuous_recessionFn (hc : IsClosed (epi f)) :
    LowerSemicontinuous (recessionFn f) :=
  lowerSemicontinuous_iff_isClosed_epi.2 (isClosed_epi_recessionFn hc)

/-- `f0⁺` is a closed function when `f` is a closed proper function. -/
theorem closedFn_recessionFn (hp : Proper f) (hc : IsClosed (epi f)) : ClosedFn (recessionFn f) :=
  (closedFn_iff_lowerSemicontinuous (recessionFn_ne_bot hp)).2 (lowerSemicontinuous_recessionFn hc)

theorem isClosed_recessionConeFn (hc : IsClosed (epi f)) : IsClosed (recessionConeFn f) := by
  have hpre : recessionConeFn f = (fun z : E => (z, (0 : ℝ))) ⁻¹' recessionCone (epi f) := by
    ext z
    exact mem_recessionConeFn_iff_mk
  rw [hpre]
  exact (isClosed_recessionCone hc).preimage (by fun_prop)

/-- **One half-line is enough**, on epigraphs: for a closed convex `f`, a single half-line inside
`epi f` already witnesses a direction of recession. -/
theorem mk_mem_recessionCone_epi_of_ray (hf : ConvexFn f) (hc : IsClosed (epi f)) (x : E) (μ : ℝ)
    {ν : ℝ} (h : ∀ a : ℝ, 0 ≤ a → f (x + a • y) ≤ ((μ + a * ν : ℝ) : EReal)) :
    ((y, ν) : E × ℝ) ∈ recessionCone (epi f) := by
  refine mem_recessionCone_of_exists_ray hf.convex_epi hc ⟨(x, μ), fun a ha => ?_⟩
  rw [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  exact mk_mem_epi.2 (h a ha)

/-- For a closed convex `f` the recession condition may be tested at a *single* point of `dom f`.
This is the sharpening that the difference-quotient formula rests on. -/
theorem recessionFn_le_coe_iff_of_isClosed (hf : ConvexFn f) (hc : IsClosed (epi f))
    (hbot : ∀ z, f z ≠ ⊥) (hx : x ∈ dom f) {ν : ℝ} :
    recessionFn f y ≤ (ν : EReal) ↔
      ∀ a : ℝ, 0 < a → f (x + a • y) ≤ f x + ((a * ν : ℝ) : EReal) := by
  refine ⟨fun h a ha => recessionFn_le_coe_iff_forall.1 h x a ha.le, fun h => ?_⟩
  obtain ⟨s, hs⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hbot x) hx
  refine recessionFn_le_coe_iff.2 (mk_mem_recessionCone_epi_of_ray hf hc x s fun a ha => ?_)
  rcases ha.eq_or_lt with rfl | ha'
  · simpa using hs.le
  · have hstep := h a ha'
    rwa [hs, ← _root_.EReal.coe_add] at hstep

/-- **The difference-quotient formula**: for a closed convex `f` and any one `x ∈ dom f`,

`(f0⁺) y = sup {(f (x + a • y) - f x) / a | a > 0}`. Closedness is what makes the answer
independent of `x`. -/
theorem recessionFn_apply_eq_iSup_inv_mul (hf : ConvexFn f) (hc : IsClosed (epi f))
    (hbot : ∀ z, f z ≠ ⊥) (hx : x ∈ dom f) (y : E) :
    recessionFn f y = ⨆ a : ℝ, ⨆ _ : 0 < a, ((a⁻¹ : ℝ) : EReal) * (f (x + a • y) - f x) := by
  refine EReal.eq_of_forall_le_coe_iff fun ν => ?_
  rw [recessionFn_le_coe_iff_of_isClosed hf hc hbot hx, iSup₂_le_iff]
  exact forall₂_congr fun a ha => (coe_inv_mul_sub_le_coe_iff (y := y) hbot hx ha).symm

/-- **The limit formula**: the difference quotient increases to `(f0⁺) y` as `a → ∞`.
Monotonicity of the quotient (`monotone_coe_inv_mul_sub`) is what turns the supremum into a
limit. -/
theorem tendsto_coe_inv_mul_sub_atTop (hf : ConvexFn f) (hc : IsClosed (epi f))
    (hbot : ∀ z, f z ≠ ⊥) (hx : x ∈ dom f) (y : E) :
    Tendsto (fun a : ℝ => ((a⁻¹ : ℝ) : EReal) * (f (x + a • y) - f x)) atTop
      (𝓝 (recessionFn f y)) := by
  rw [tendsto_order]
  constructor
  · intro b hb
    rw [recessionFn_apply_eq_iSup_inv_mul hf hc hbot hx y, lt_iSup_iff] at hb
    obtain ⟨a₀, hb⟩ := hb
    rw [lt_iSup_iff] at hb
    obtain ⟨ha₀, hb⟩ := hb
    filter_upwards [eventually_ge_atTop a₀] with a ha
    exact lt_of_lt_of_le hb (monotone_coe_inv_mul_sub hf hbot hx y ha₀ ha)
  · intro b hb
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    refine lt_of_le_of_lt ?_ hb
    rw [recessionFn_apply_eq_iSup_inv_mul hf hc hbot hx y]
    exact le_iSup₂ (f := fun a (_ : 0 < a) => ((a⁻¹ : ℝ) : EReal) * (f (x + a • y) - f x)) a ha

/-- When `f` is closed, a single `x ∈ dom f` along which `f` is nonincreasing already forces
`(f0⁺) y ≤ 0`. -/
theorem recessionFn_nonpos_of_antitone (hf : ClosedProperConvexFn f)
    (hx : x ∈ dom f) (h : Antitone fun a : ℝ => f (x + a • y)) : recessionFn f y ≤ 0 := by
  have h0 : recessionFn f y ≤ ((0 : ℝ) : EReal) := by
    rw [recessionFn_le_coe_iff_of_isClosed hf.convex hf.isClosed_epi hf.proper.ne_bot hx]
    intro a ha
    have hstep := h ha.le
    simp only [zero_smul, add_zero] at hstep
    simpa using hstep
  rwa [_root_.EReal.coe_zero] at h0

/-- For a closed `f`, a single `x ∈ dom f` along which `f` is affine with slope `ν` already forces
`(f0⁺) y = ν` and `(f0⁺) (-y) = -ν`. -/
theorem recessionFn_eq_of_affine_along (hf : ClosedProperConvexFn f)
    (hx : x ∈ dom f) {ν : ℝ} (h : ∀ a : ℝ, f (x + a • y) = f x + ((a * ν : ℝ) : EReal)) :
    recessionFn f y = (ν : EReal) ∧ recessionFn f (-y) = ((-ν : ℝ) : EReal) := by
  obtain ⟨s, hs⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hf.proper.ne_bot x) hx
  refine (mk_mem_linealitySpace_epi_iff hf.proper).1 (mem_linealitySpace.2 ⟨?_, ?_⟩)
  · refine mk_mem_recessionCone_epi_of_ray hf.convex hf.isClosed_epi x s fun a _ => ?_
    rw [h a, hs, ← _root_.EReal.coe_add]
  · refine (mk_mem_recessionCone_epi_of_ray hf.convex hf.isClosed_epi x s fun a _ => ?_ :
      ((-y, -ν) : E × ℝ) ∈ recessionCone (epi f))
    have hstep := h (-a)
    rw [neg_smul, ← smul_neg, hs, ← _root_.EReal.coe_add] at hstep
    rw [hstep, show s + -a * ν = s + a * -ν by ring]

/-- For a closed convex `f`, every nonempty level set `{x | f x ≤ α}` has the same recession cone,
namely the recession cone of `f`. -/
theorem recessionCone_setOf_le (hf : ConvexFn f) (hc : IsClosed (epi f)) {α : ℝ}
    (hne : {z : E | f z ≤ (α : EReal)}.Nonempty) :
    recessionCone {z : E | f z ≤ (α : EReal)} = recessionConeFn f := by
  ext z
  constructor
  · intro hz
    obtain ⟨w, hw⟩ := hne
    refine mem_recessionConeFn_iff_mk.2 (mk_mem_recessionCone_epi_of_ray hf hc w α fun a ha => ?_)
    have hmem : f (w + a • z) ≤ (α : EReal) := hz w hw a ha
    rwa [show α + a * 0 = α by ring]
  · intro hz w hw a ha
    exact le_trans (add_smul_le_of_recessionFn_nonpos hz w ha) hw

/-- **The lineality half**: every nonempty level set of a closed convex `f` has the constancy
space of `f` as its lineality space. -/
theorem linealitySpace_setOf_le (hf : ConvexFn f) (hc : IsClosed (epi f)) {α : ℝ}
    (hne : {z : E | f z ≤ (α : EReal)}.Nonempty) :
    linealitySpace {z : E | f z ≤ (α : EReal)} = constancySpace f := by
  simp only [linealitySpace, constancySpace, recessionCone_setOf_le hf hc hne]

/-! #### The limit of the right scalar multiples

`(f0⁺) y = lim_{a ↓ 0} (fa) y` is proved here directly from the recession calculus, rather than
through the homogenisation `hom f`: the latter route would need `cl (hom f)`, since
`hom f (0, ·) = δ(· | 0)` and not `f0⁺`. The proof splits into the two halves of `tendsto_order`,
and only the *upper* half needs a point of `dom f` on the ray through `y`. -/

/-- The lower half, and the half that carries the closedness hypothesis: no `fa` can dip below
`(f0⁺) y` in the limit. It is the sequential criterion for a direction of recession applied to
`aₙ⁻¹ • (y, β)` in `epi f`. -/
theorem eventually_lt_smulRight (hf : ConvexFn f) (hc : IsClosed (epi f)) {b : EReal}
    (hb : b < recessionFn f y) : ∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ), b < smulRight f a y := by
  have hpos : ∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ), 0 < a := self_mem_nhdsWithin
  obtain ⟨β, hbβ, hβL⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 hb
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hfreq : ∃ᶠ a : ℝ in 𝓝[>] (0 : ℝ), 0 < a ∧ smulRight f a y ≤ (β : EReal) :=
    (hcon.and_eventually hpos).mono fun a ha =>
      ⟨ha.2, le_of_lt (lt_of_le_of_lt (not_lt.1 ha.1) hbβ)⟩
  obtain ⟨u, hu, hup⟩ := Filter.exists_seq_forall_of_frequently hfreq
  have hu0 : Tendsto u atTop (𝓝 (0 : ℝ)) := hu.mono_right nhdsWithin_le_nhds
  have hmem : ∀ n, (u n)⁻¹ • ((y, β) : E × ℝ) ∈ epi f := by
    intro n
    have hun := (hup n).1
    have hle := (hup n).2
    rw [smulRight_apply_pos hun] at hle
    rw [Prod.smul_mk, smul_eq_mul]
    refine mk_mem_epi.2 ?_
    have h3 : (((u n)⁻¹ : ℝ) : EReal) * (((u n : ℝ) : EReal) * f ((u n)⁻¹ • y))
        ≤ (((u n)⁻¹ : ℝ) : EReal) * ((β : ℝ) : EReal) :=
      mul_le_mul_of_nonneg_left hle (by exact_mod_cast (inv_pos.2 hun).le)
    rwa [← mul_assoc, EReal.coe_mul_coe, inv_mul_cancel₀ hun.ne', _root_.EReal.coe_one,
      one_mul, EReal.coe_mul_coe] at h3
  have hconst : (fun n => u n • ((u n)⁻¹ • ((y, β) : E × ℝ))) = fun _ => ((y, β) : E × ℝ) := by
    funext n
    rw [smul_smul, mul_inv_cancel₀ (hup n).1.ne', one_smul]
  have hmemrec : ((y, β) : E × ℝ) ∈ recessionCone (epi f) :=
    mem_recessionCone_of_tendsto hf.convex_epi hc hmem (fun n => (hup n).1) hu0
      (by rw [hconst]; exact tendsto_const_nhds)
  exact absurd (recessionFn_le_coe_iff.2 hmemrec) (not_le.2 hβL)

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- The upper half, from a point `θ • y ∈ dom f` on the line through `y`: `(fa) y` eventually
stays below any bound exceeding `(f0⁺) y`. `θ = 1` is the case `y ∈ dom f` and `θ = 0` the case
`0 ∈ dom f`; no other point of `dom f` helps, because the endpoint of the half-line must lie on
the line through `y`. This half needs no topology on `E`: it is the one-step recession test plus
one limit in `ℝ`. -/
theorem eventually_smulRight_lt (hp : Proper f) {θ : ℝ} (hθ : θ • y ∈ dom f) {b : EReal}
    (hb : recessionFn f y < b) :
    ∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ), smulRight f a y < b := by
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot (θ • y)) hθ
  obtain ⟨β, hLβ, hβb⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 hb
  obtain ⟨γ, hβγ, hγb⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 hβb
  have hβγ' : β < γ := by exact_mod_cast hβγ
  have hray := mk_mem_recessionCone_epi.1 (recessionFn_le_coe_iff.1 hLβ.le) (θ • y) r hr.le
  have hcont : Tendsto (fun a : ℝ => a * r + (1 - a * θ) * β) (𝓝[>] (0 : ℝ)) (𝓝 β) := by
    have hcf : Continuous fun a : ℝ => a * r + (1 - a * θ) * β := by fun_prop
    simpa using (hcf.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hpos : ∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ), 0 < a := self_mem_nhdsWithin
  have hlt : ∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ), a * θ < 1 := by
    have hcf : Continuous fun a : ℝ => a * θ := by fun_prop
    have h0 : Tendsto (fun a : ℝ => a * θ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using (hcf.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    exact h0.eventually_lt_const one_pos
  filter_upwards [hcont.eventually_lt_const hβγ', hpos, hlt] with a hva hapos haθ
  have hid : a * a⁻¹ = 1 := mul_inv_cancel₀ hapos.ne'
  have hinvpos : (0 : ℝ) < a⁻¹ := inv_pos.2 hapos
  have hnn : 0 ≤ a⁻¹ - θ := by nlinarith
  have harg : θ • y + (a⁻¹ - θ) • y = a⁻¹ • y := by
    rw [← add_smul]
    congr 1
    ring
  have hkey : f (a⁻¹ • y) ≤ ((r + (a⁻¹ - θ) * β : ℝ) : EReal) := by
    have hstep := hray (a⁻¹ - θ) hnn
    rwa [harg] at hstep
  rw [smulRight_apply_pos hapos]
  have h2 : ((a : ℝ) : EReal) * f (a⁻¹ • y)
      ≤ ((a : ℝ) : EReal) * ((r + (a⁻¹ - θ) * β : ℝ) : EReal) :=
    mul_le_mul_of_nonneg_left hkey (by exact_mod_cast hapos.le)
  refine lt_of_le_of_lt h2 ?_
  rw [EReal.coe_mul_coe,
    show a * (r + (a⁻¹ - θ) * β) = a * r + (1 - a * θ) * β by field_simp]
  exact lt_trans (by exact_mod_cast hva) hγb

/-- For a closed proper convex `f`, the recession function is the limit of the right scalar
multiples `fa` as `a ↓ 0`, at every `y ∈ dom f` — and, by
`tendsto_smulRight_recessionFn_of_zero_mem_dom`, at *every* `y` when `0 ∈ dom f`. -/
theorem tendsto_smulRight_recessionFn (hf : ClosedProperConvexFn f) (hy : y ∈ dom f) :
    Tendsto (fun a : ℝ => smulRight f a y) (𝓝[>] (0 : ℝ)) (𝓝 (recessionFn f y)) := by
  rw [tendsto_order]
  exact ⟨fun _ hb => eventually_lt_smulRight hf.convex hf.isClosed_epi hb,
    fun _ hb => eventually_smulRight_lt hf.proper (θ := 1) (by rwa [one_smul]) hb⟩

/-- **Global form**: when `0 ∈ dom f` the limit formula holds at every `y`, with no condition on
`y` at all. -/
theorem tendsto_smulRight_recessionFn_of_zero_mem_dom (hf : ClosedProperConvexFn f)
    (h0 : (0 : E) ∈ dom f) (y : E) :
    Tendsto (fun a : ℝ => smulRight f a y) (𝓝[>] (0 : ℝ)) (𝓝 (recessionFn f y)) := by
  rw [tendsto_order]
  exact ⟨fun _ hb => eventually_lt_smulRight hf.convex hf.isClosed_epi hb,
    fun _ hb => eventually_smulRight_lt hf.proper (θ := 0) (by rwa [zero_smul]) hb⟩

end Topological

/-! ### Slices of a function of two variables

A closed convex function of two variables has the **same** recession function on every slice
`x ↦ G (u, x)` with non-empty effective domain: it is "one half-line is enough", read on the
epigraph. -/

section Slice

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [TopologicalSpace U] [IsTopologicalAddGroup U]
  [ContinuousSMul ℝ U] [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [ContinuousSMul ℝ X] {G : U × X → EReal} {u₀ : U} {x₀ y : X} {ν : ℝ}

/-- A recession direction of *one* slice of a closed convex `G` is a recession direction of *every*
slice, with the same bound. The slice inequality at a single point exhibits a half-line of `epi G`
in the direction `((0, y), ν)`, and for a closed convex set one half-line is enough.
No hypothesis is placed on `u`: when `G (u, ·) ≡ ⊤` the conclusion holds vacuously. -/
theorem recessionFn_le_coe_of_slice (hG : ConvexFn G) (hc : IsClosed (epi G))
    (hx₀ : G (u₀, x₀) ≠ ⊤) (h : recessionFn (fun x => G (u₀, x)) y ≤ (ν : EReal)) (u : U) :
    recessionFn (fun x => G (u, x)) y ≤ (ν : EReal) := by
  obtain ⟨μ, hμ, -⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 (lt_top_iff_ne_top.2 hx₀)
  have hdir : (((0 : U), y), ν) ∈ recessionCone (epi G) := by
    refine mem_recessionCone_of_exists_ray hG.convex_epi hc ⟨((u₀, x₀), μ), fun a ha => ?_⟩
    have hstep := recessionFn_le_coe_iff_forall.1 h x₀ a ha
    have hbound : G (u₀, x₀ + a • y) ≤ ((μ + a * ν : ℝ) : EReal) := by
      refine hstep.trans ?_
      rw [_root_.EReal.coe_add]
      exact add_le_add hμ.le le_rfl
    simpa [Prod.smul_mk, smul_zero] using hbound
  refine recessionFn_le_coe_iff.2 fun p hp a ha => ?_
  have hmem : ((u, p.1), p.2) ∈ epi G := hp
  simpa [Prod.smul_mk, smul_zero] using hdir _ hmem a ha

/-- **One recession function for all slices**: a closed convex function of two variables has the
same recession function on any two slices with non-empty effective domain. -/
theorem recessionFn_slice_eq (hG : ConvexFn G) (hc : IsClosed (epi G)) {u₁ : U}
    (h₀ : ∃ x, G (u₀, x) ≠ ⊤) (h₁ : ∃ x, G (u₁, x) ≠ ⊤) :
    recessionFn (fun x => G (u₀, x)) = recessionFn (fun x => G (u₁, x)) := by
  obtain ⟨x₀, hx₀⟩ := h₀
  obtain ⟨x₁, hx₁⟩ := h₁
  funext z
  refine EReal.eq_of_forall_le_coe_iff fun r => ⟨fun h => ?_, fun h => ?_⟩
  · exact recessionFn_le_coe_of_slice hG hc hx₀ h u₁
  · exact recessionFn_le_coe_of_slice hG hc hx₁ h u₀

end Slice

/-! ### Bounded level sets -/

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

/-- For a closed convex `f`, if one nonempty level set is bounded then every nonempty level set
is. Finite-dimensionality enters only through the criterion for boundedness. -/
theorem isBounded_setOf_le (hf : ConvexFn f) (hc : IsClosed (epi f)) {α β : ℝ}
    (hneα : {z : E | f z ≤ (α : EReal)}.Nonempty)
    (hbd : Bornology.IsBounded {z : E | f z ≤ (α : EReal)})
    (hneβ : {z : E | f z ≤ (β : EReal)}.Nonempty) :
    Bornology.IsBounded {z : E | f z ≤ (β : EReal)} := by
  have hclα : IsClosed {z : E | f z ≤ (α : EReal)} :=
    lowerSemicontinuous_iff_isClosed_le.1
      (lowerSemicontinuous_iff_isClosed_epi.2 hc) α
  have hclβ : IsClosed {z : E | f z ≤ (β : EReal)} :=
    lowerSemicontinuous_iff_isClosed_le.1
      (lowerSemicontinuous_iff_isClosed_epi.2 hc) β
  have hzero : recessionCone {z : E | f z ≤ (α : EReal)} = {0} :=
    (isBounded_iff_recessionCone_eq_zero (hf.convex_le _) hclα hneα).1 hbd
  refine (isBounded_iff_recessionCone_eq_zero (hf.convex_le _) hclβ hneβ).2 ?_
  rw [recessionCone_setOf_le hf hc hneβ, ← recessionCone_setOf_le hf hc hneα]
  exact hzero

end FiniteDimensional

end ConvexAnalysis
