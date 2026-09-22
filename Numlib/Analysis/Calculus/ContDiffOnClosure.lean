/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Calculus.ContDiff.Defs`, beside `ContDiffOn`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Numlib.Analysis.Calculus.AddTorsor.AffineMap

/-!
# Functions of class `C^n` up to the boundary

`ContDiffOnClosure 𝕜 n f s` is the class `C^n(s̄)` of the partial differential equations
literature — Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
chapter 9, footnote 16: `f` is `C^n` on the open set `s` and each of its derivatives of order
`m ≤ n` extends continuously to the closure of `s`.

This is weaker than Mathlib's `ContDiffOn 𝕜 n f (closure s)`, which asks at every boundary point
for a Taylor expansion *within* the closure; the two agree on regular domains but the Mathlib
notion is the wrong hypothesis to write when a book says `u ∈ C^k(Ω̄)`. The implication from the
Mathlib notion, `ContDiffOn.contDiffOnClosure`, holds for every open `s`, without any unique
differentiability of the closure: the continuous extension of `D^m f` is assembled from the local
Taylor data of `ContDiffWithinAt` by taking limits along `s`.

Two readers: `s = Ω` a spatial domain, for the conclusions `u ∈ C^k(Ω̄)` of the Sobolev
embeddings and of elliptic regularity; and `s = Ω ×ˢ I` for a time interval `I`, for the
space–time classes `C^∞(Ω̄ × [ε, ∞))` of the evolution equations.

## Main definitions

* `ContDiffOnClosure 𝕜 n f s`: `f ∈ C^n(s̄)`.

## Main statements

* `ContDiffOnClosure.of_le`, `ContDiffOnClosure.mono`: monotone in the order and in the set;
* `ContDiffOnClosure.continuousOn_closure`: `f` itself extends continuously to `closure s`;
* `ContDiffOn.contDiffOnClosure`: `ContDiffOn 𝕜 n f (closure s)` implies `f ∈ C^n(s̄)` for
  open `s`;
* `contDiffOnClosure_one_iff`: `f ∈ C¹(s̄)` iff `f` is `C¹` on `s` and both `f` and `fderiv 𝕜 f`
  extend continuously to `closure s` — the working form of the class at order one, through which
  the stability properties below are proved;
* the algebra of `C¹(s̄)` on an open `s`: `ContDiffOnClosure.smul`, `mul`, `const`, `smul_const`,
  `continuousLinearMap_comp`, `clm_comp_comp_affine`, `comp_affineIsometryEquiv`, and the
  locality on the support `ContDiffOnClosure.congr_set_of_tsupport_subset`;
* bounds on the derivative: `ContDiffOnClosure.exists_norm_fderiv_le` (on a bounded set) and
  `exists_norm_fderiv_le_of_hasCompactSupport`;
* `ContDiffOnClosure.exists_continuousOn_fderiv_fderiv`: the second derivative of a `C²(s̄)`
  function extends continuously.

The extension of each derivative is unique on `closure s`, `s` being dense there:
`Set.EqOn.of_subset_closure` is the statement.

## References

[brezis2011functional], chapter 9, footnote 16.
-/

open Filter Set Topology

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {X F : Type*} [NormedAddCommGroup X]
  [NormedSpace 𝕜 X] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **The class `C^n(s̄)`**: `f` is `C^n` on `s` and each derivative `D^m f`, `m ≤ n`, has a
continuous extension to `closure s`. This is the class of [brezis2011functional], chapter 9,
footnote 16, meant for an open `s`. -/
def ContDiffOnClosure (n : WithTop ℕ∞) (f : X → F) (s : Set X) : Prop :=
  ContDiffOn 𝕜 n f s ∧ ∀ m : ℕ, (m : WithTop ℕ∞) ≤ n →
    ∃ g : X → X [×m]→L[𝕜] F, ContinuousOn g (closure s) ∧ EqOn g (iteratedFDeriv 𝕜 m f) s

variable {𝕜} {n : WithTop ℕ∞} {f : X → F} {s : Set X}

namespace ContDiffOnClosure

theorem contDiffOn (h : ContDiffOnClosure 𝕜 n f s) : ContDiffOn 𝕜 n f s := h.1

/-- The derivative of order `m ≤ n` of a function of class `C^n(s̄)` extends continuously to
`closure s`. -/
theorem exists_continuousOn_closure_iteratedFDeriv (h : ContDiffOnClosure 𝕜 n f s) {m : ℕ}
    (hm : (m : WithTop ℕ∞) ≤ n) :
    ∃ g : X → X [×m]→L[𝕜] F, ContinuousOn g (closure s) ∧ EqOn g (iteratedFDeriv 𝕜 m f) s :=
  h.2 m hm

/-- `C^n(s̄) ⊆ C^m(s̄)` for `m ≤ n`. -/
theorem of_le {m : WithTop ℕ∞} (h : ContDiffOnClosure 𝕜 n f s) (hmn : m ≤ n) :
    ContDiffOnClosure 𝕜 m f s :=
  ⟨h.1.of_le hmn, fun k hk ↦ h.2 k (hk.trans hmn)⟩

/-- `C^n(s̄)` restricts to subsets: the extensions restrict along `closure s' ⊆ closure s`. This
is how `C^∞(Ω̄ × (0, ∞))` yields `C^∞(Ω̄ × [ε, ∞))` for every `ε > 0`. -/
theorem mono {s' : Set X} (h : ContDiffOnClosure 𝕜 n f s) (hs : s' ⊆ s) :
    ContDiffOnClosure 𝕜 n f s' :=
  ⟨h.1.mono hs, fun m hm ↦
    let ⟨g, hgc, hge⟩ := h.2 m hm
    ⟨g, hgc.mono (closure_mono hs), hge.mono hs⟩⟩

/-- A function of class `C^n(s̄)` extends continuously to `closure s`. -/
theorem continuousOn_closure (h : ContDiffOnClosure 𝕜 n f s) :
    ∃ g : X → F, ContinuousOn g (closure s) ∧ EqOn g f s := by
  obtain ⟨g₀, hgc, hge⟩ := h.2 0 (by simp)
  refine ⟨fun x ↦ continuousMultilinearCurryFin0 𝕜 X F (g₀ x),
    (continuousMultilinearCurryFin0 𝕜 X F).continuous.comp_continuousOn hgc, fun x hx ↦ ?_⟩
  change continuousMultilinearCurryFin0 𝕜 X F (g₀ x) = f x
  rw [hge hx, iteratedFDeriv_zero_eq_comp, Function.comp_apply]
  exact (continuousMultilinearCurryFin0 𝕜 X F).apply_symm_apply (f x)

end ContDiffOnClosure

/-- **`ContDiffOn` on the closure implies `C^n(s̄)`**, for every open `s`, with no unique
differentiability of `closure s` assumed. The extension of `D^m f` is
`y ↦ lim_{z → y, z ∈ s} D^m f z`: near each point of `closure s` the Taylor data of
`ContDiffWithinAt` supply a continuous function agreeing with `D^m f` on `s`, so the limit exists
and is continuous. -/
theorem ContDiffOn.contDiffOnClosure (hs : IsOpen s) (h : ContDiffOn 𝕜 n f (closure s)) :
    ContDiffOnClosure 𝕜 n f s := by
  refine ⟨h.mono subset_closure, fun m hm ↦ ?_⟩
  -- local continuous extensions of `D^m f`, from the Taylor data
  have key : ∀ x ∈ closure s, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ g : X → X [×m]→L[𝕜] F,
      ContinuousOn g (closure s ∩ V) ∧ EqOn g (iteratedFDeriv 𝕜 m f) (s ∩ V) := by
    intro x hx
    obtain ⟨u, hu, p, hp⟩ := contDiffWithinAt_nat.1 ((h x hx).of_le hm)
    rw [insert_eq_of_mem hx] at hu
    obtain ⟨V, hVo, hxV, hVu⟩ := mem_nhdsWithin.1 hu
    refine ⟨V, hVo, hxV, fun y ↦ p y m, (hp.cont m le_rfl).mono fun y hy ↦ hVu ⟨hy.2, hy.1⟩,
      fun y hy ↦ ?_⟩
    have hsub : s ∩ V ⊆ u := fun z hz ↦ hVu ⟨hz.2, subset_closure hz.1⟩
    change p y m = iteratedFDeriv 𝕜 m f y
    rw [(hp.mono hsub).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl (hs.inter hVo).uniqueDiffOn
      hy, iteratedFDerivWithin_of_isOpen m (hs.inter hVo) hy]
  choose! V hVo hxV g hgc hge using key
  -- the global extension, as a limit along `s`
  set G : X → X [×m]→L[𝕜] F := fun y ↦ limUnder (𝓝[s] y) (iteratedFDeriv 𝕜 m f) with hGdef
  have hG : ∀ x ∈ closure s, EqOn G (g x) (closure s ∩ V x) := by
    intro x hx y hy
    have hne : (𝓝[s] y).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hy.1
    have h1 : Tendsto (g x) (𝓝[closure s ∩ V x] y) (𝓝 (g x y)) :=
      (hgc x hx).continuousWithinAt hy
    have h2 : 𝓝[s] y ≤ 𝓝[closure s ∩ V x] y :=
      nhdsWithin_le_of_mem (mem_nhdsWithin.2
        ⟨V x, hVo x hx, hy.2, fun z hz ↦ ⟨subset_closure hz.2, hz.1⟩⟩)
    have h3 : g x =ᶠ[𝓝[s] y] iteratedFDeriv 𝕜 m f := by
      filter_upwards [inter_mem_nhdsWithin s ((hVo x hx).mem_nhds hy.2)] with z hz
      exact hge x hx hz
    exact ((h1.mono_left h2).congr' h3).limUnder_eq
  refine ⟨G, fun y hy ↦ ?_, fun y hy ↦ ?_⟩
  · have hmem : V y ∈ 𝓝[closure s] y :=
      mem_nhdsWithin_of_mem_nhds ((hVo y hy).mem_nhds (hxV y hy))
    refine (continuousWithinAt_inter' hmem).1 ?_
    exact ((hgc y hy).continuousWithinAt ⟨hy, hxV y hy⟩).congr (fun z hz ↦ hG y hy hz)
      (hG y hy ⟨hy, hxV y hy⟩)
  · have hy' : y ∈ closure s := subset_closure hy
    rw [hG y hy' ⟨hy', hxV y hy'⟩, hge y hy' ⟨hy, hxV y hy'⟩]

/-! ### The class `C¹(s̄)` through the derivative -/

section One

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- The first derivative tensor is the derivative, read through `continuousMultilinearCurryFin1`
(the real case is `iteratedFDeriv_one_eq_symm_fderiv` of
`Numlib/Analysis/Sobolev/Friedrichs.lean`). -/
theorem iteratedFDeriv_one_eq_symm_fderiv' (f : X → F) (x : X) :
    iteratedFDeriv 𝕜 1 f x = (continuousMultilinearCurryFin1 𝕜 X F).symm (fderiv 𝕜 f x) :=
  ContinuousMultilinearMap.ext fun m ↦ by simp

/-- **The class `C¹(s̄)` through the derivative**: `f ∈ C¹(s̄)` iff `f` is `C¹` on `s` and both `f`
and `fderiv 𝕜 f` extend continuously to `closure s`. -/
theorem contDiffOnClosure_one_iff :
    ContDiffOnClosure 𝕜 1 f s ↔ ContDiffOn 𝕜 1 f s ∧
      (∃ g : X → F, ContinuousOn g (closure s) ∧ EqOn g f s) ∧
      ∃ g' : X → X →L[𝕜] F, ContinuousOn g' (closure s) ∧ EqOn g' (fderiv 𝕜 f) s := by
  constructor
  · intro h
    refine ⟨h.1, h.continuousOn_closure, ?_⟩
    obtain ⟨g, hgc, hge⟩ := h.2 1 le_rfl
    refine ⟨fun x ↦ continuousMultilinearCurryFin1 𝕜 X F (g x),
      (continuousMultilinearCurryFin1 𝕜 X F).continuous.comp_continuousOn hgc, fun x hx ↦ ?_⟩
    change continuousMultilinearCurryFin1 𝕜 X F (g x) = fderiv 𝕜 f x
    rw [hge hx, iteratedFDeriv_one_eq_symm_fderiv', LinearIsometryEquiv.apply_symm_apply]
  · rintro ⟨h, ⟨g, hgc, hge⟩, ⟨g', hgc', hge'⟩⟩
    refine ⟨h, fun m hm ↦ ?_⟩
    have hm' : m ≤ 1 := by exact_mod_cast hm
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hm' with rfl | rfl
    · refine ⟨fun x ↦ (continuousMultilinearCurryFin0 𝕜 X F).symm (g x),
        (continuousMultilinearCurryFin0 𝕜 X F).symm.continuous.comp_continuousOn hgc,
        fun x hx ↦ ?_⟩
      change (continuousMultilinearCurryFin0 𝕜 X F).symm (g x) = iteratedFDeriv 𝕜 0 f x
      rw [hge hx, iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    · refine ⟨fun x ↦ (continuousMultilinearCurryFin1 𝕜 X F).symm (g' x),
        (continuousMultilinearCurryFin1 𝕜 X F).symm.continuous.comp_continuousOn hgc',
        fun x hx ↦ ?_⟩
      change (continuousMultilinearCurryFin1 𝕜 X F).symm (g' x) = iteratedFDeriv 𝕜 1 f x
      rw [hge' hx, iteratedFDeriv_one_eq_symm_fderiv']

/-- The second derivative of a function of class `C²(s̄)` extends continuously to `closure s`. -/
theorem ContDiffOnClosure.exists_continuousOn_fderiv_fderiv (h : ContDiffOnClosure 𝕜 2 f s) :
    ∃ G : X → X →L[𝕜] X →L[𝕜] F, ContinuousOn G (closure s) ∧
      EqOn G (fderiv 𝕜 (fderiv 𝕜 f)) s := by
  obtain ⟨g₂, hc, he⟩ := h.2 2 le_rfl
  let C : (X [×1]→L[𝕜] F) →L[𝕜] (X →L[𝕜] F) :=
    (continuousMultilinearCurryFin1 𝕜 X F : (X [×1]→L[𝕜] F) →L[𝕜] (X →L[𝕜] F))
  let L : (X [×2]→L[𝕜] F) →L[𝕜] (X →L[𝕜] X [×1]→L[𝕜] F) :=
    (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin 2 ↦ X) F :
      (X [×2]→L[𝕜] F) →L[𝕜] (X →L[𝕜] X [×1]→L[𝕜] F))
  refine ⟨fun x ↦ ContinuousLinearMap.compL 𝕜 X (X [×1]→L[𝕜] F) (X →L[𝕜] F) C (L (g₂ x)), ?_,
    fun x hx ↦ ?_⟩
  · exact ((ContinuousLinearMap.compL 𝕜 X (X [×1]→L[𝕜] F) (X →L[𝕜] F) C).continuous.comp
      L.continuous).comp_continuousOn hc
  · ext w v
    simp only [ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply, he hx]
    change continuousMultilinearCurryFin1 𝕜 X F
      (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin 2 ↦ X) F (iteratedFDeriv 𝕜 2 f x) w) v
      = _
    rw [continuousMultilinearCurryFin1_apply, continuousMultilinearCurryLeftEquiv_apply,
      iteratedFDeriv_two_apply]
    simp

namespace ContDiffOnClosure

/-- **`C¹(s̄)` is closed under the product of a scalar function with a vector function**, on an
open set `s`: `D(u v) = u Dv + (Du) v` on `s`, and the continuous extensions of `u, v, Du, Dv`
to `closure s` combine into one of `D(u v)`. -/
theorem smul (hs : IsOpen s) {u : X → 𝕜} {v : X → F} (hu : ContDiffOnClosure 𝕜 1 u s)
    (hv : ContDiffOnClosure 𝕜 1 v s) : ContDiffOnClosure 𝕜 1 (fun x ↦ u x • v x) s := by
  rw [contDiffOnClosure_one_iff] at hu hv ⊢
  obtain ⟨hu, ⟨u₁, hu₁c, hu₁e⟩, ⟨u₁', hu₁c', hu₁e'⟩⟩ := hu
  obtain ⟨hv, ⟨v₁, hv₁c, hv₁e⟩, ⟨v₁', hv₁c', hv₁e'⟩⟩ := hv
  refine ⟨hu.smul hv, ⟨fun x ↦ u₁ x • v₁ x, hu₁c.smul hv₁c, fun x hx ↦ by
    simp only [hu₁e hx, hv₁e hx]⟩,
    ⟨fun x ↦ u₁ x • v₁' x + (u₁' x).smulRight (v₁ x), ?_, fun x hx ↦ ?_⟩⟩
  · refine (hu₁c.smul hv₁c').add ?_
    exact (ContinuousLinearMap.smulRightL 𝕜 X F).continuous₂.comp_continuousOn
      (hu₁c'.prodMk hv₁c)
  · have hux : DifferentiableAt 𝕜 u x :=
      (hu.differentiableOn one_ne_zero).differentiableAt (hs.mem_nhds hx)
    have hvx : DifferentiableAt 𝕜 v x :=
      (hv.differentiableOn one_ne_zero).differentiableAt (hs.mem_nhds hx)
    simp only [hu₁e hx, hv₁e hx, hu₁e' hx, hv₁e' hx]
    exact (fderiv_fun_smul hux hvx).symm

/-- **`C¹(s̄)` is closed under products of scalar functions**, on an open set `s`. -/
theorem mul (hs : IsOpen s) {u v : X → 𝕜} (hu : ContDiffOnClosure 𝕜 1 u s)
    (hv : ContDiffOnClosure 𝕜 1 v s) : ContDiffOnClosure 𝕜 1 (fun x ↦ u x * v x) s :=
  hu.smul hs hv

/-- A constant function is of class `C¹(s̄)`. -/
theorem const (c : F) : ContDiffOnClosure 𝕜 1 (fun _ : X ↦ c) s := by
  rw [contDiffOnClosure_one_iff]
  exact ⟨contDiffOn_const, ⟨fun _ ↦ c, continuousOn_const, fun _ _ ↦ rfl⟩,
    ⟨fun _ ↦ 0, continuousOn_const, fun x _ ↦ (fderiv_const_apply c).symm⟩⟩

/-- **`C¹(s̄)` is closed under multiplication by a fixed vector**, on an open set `s`. -/
theorem smul_const (hs : IsOpen s) {u : X → 𝕜} (hu : ContDiffOnClosure 𝕜 1 u s) (c : F) :
    ContDiffOnClosure 𝕜 1 (fun x ↦ u x • c) s :=
  hu.smul hs (const c)

/-- **The derivative of a function of class `C¹(s̄)` is bounded on a bounded set `s`**: it extends
continuously to the compact closure. -/
theorem exists_norm_fderiv_le [ProperSpace X] (hf : ContDiffOnClosure 𝕜 1 f s)
    (hs : Bornology.IsBounded s) : ∃ C, ∀ x ∈ s, ‖fderiv 𝕜 f x‖ ≤ C := by
  obtain ⟨-, -, g', hg'c, hg'e⟩ := contDiffOnClosure_one_iff.1 hf
  obtain ⟨C, hC⟩ := hs.isCompact_closure.exists_bound_of_continuousOn hg'c
  exact ⟨C, fun x hx ↦ by rw [← hg'e hx]; exact hC x (subset_closure hx)⟩

/-- **A function of class `C¹(s̄)` with compact support has a bounded derivative on `s`**: the
continuous extension of `fderiv 𝕜 f` is bounded on the compact `closure s ∩ tsupport f`, and
`fderiv 𝕜 f = 0` off `tsupport f`. Compare `ContDiffOn.exists_norm_fderiv_le_of_isCompact` of
`Numlib/Analysis/Sobolev/Chart.lean`, which bounds the derivative on the interior of a compact
set, and `exists_norm_fderiv_le`, which asks for `s` bounded instead. -/
theorem exists_norm_fderiv_le_of_hasCompactSupport (hf : ContDiffOnClosure 𝕜 1 f s)
    (hfc : HasCompactSupport f) : ∃ M, ∀ x ∈ s, ‖fderiv 𝕜 f x‖ ≤ M := by
  obtain ⟨-, -, G, hGc, hGe⟩ := contDiffOnClosure_one_iff.1 hf
  obtain ⟨C, hC⟩ := (hfc.inter_left isClosed_closure).exists_bound_of_continuousOn
    (hGc.mono inter_subset_left)
  refine ⟨max C 0, fun x hx ↦ ?_⟩
  by_cases hxs : x ∈ tsupport f
  · rw [← hGe hx]
    exact (hC x ⟨subset_closure hx, hxs⟩).trans (le_max_left _ _)
  · rw [fderiv_of_notMem_tsupport 𝕜 hxs, norm_zero]
    exact le_max_right _ _

/-- **`C¹(s̄)` is stable under a continuous linear map on the left**, on an open set `s`: the
extensions of `f` and `Df` compose with `L`. -/
theorem continuousLinearMap_comp (hs : IsOpen s) (hf : ContDiffOnClosure 𝕜 1 f s) (L : F →L[𝕜] G) :
    ContDiffOnClosure 𝕜 1 (fun x ↦ L (f x)) s := by
  rw [contDiffOnClosure_one_iff] at hf ⊢
  obtain ⟨hf, ⟨g₀, hg₀c, hg₀e⟩, ⟨g₁, hg₁c, hg₁e⟩⟩ := hf
  refine ⟨hf.continuousLinearMap_comp L, ⟨fun x ↦ L (g₀ x), L.continuous.comp_continuousOn hg₀c,
    fun x hx ↦ by simp only [hg₀e hx]⟩, ⟨fun x ↦ L.comp (g₁ x), continuousOn_const.clm_comp hg₁c,
    fun x hx ↦ ?_⟩⟩
  have hx' : DifferentiableAt 𝕜 f x :=
    (hf.differentiableOn one_ne_zero).differentiableAt (hs.mem_nhds hx)
  simp only [hg₁e hx]
  exact (L.hasFDerivAt.comp x hx'.hasFDerivAt).fderiv.symm

end ContDiffOnClosure

/-- A function continuous on `closure s` and vanishing on `s` outside a closed set `K` vanishes
on `closure s` outside `K`: `closure s \ K` lies in the closure of `s \ K`. -/
theorem ContinuousOn.eq_zero_of_notMem_of_forall {Y : Type*} [TopologicalSpace Y] {φ : Y → G}
    {s K : Set Y} (hφ : ContinuousOn φ (closure s)) (hK : IsClosed K)
    (h : ∀ y ∈ s, y ∉ K → φ y = 0) {y : Y} (hy : y ∈ closure s) (hyK : y ∉ K) : φ y = 0 := by
  have hsub : closure s ∩ Kᶜ ⊆ closure (s ∩ Kᶜ) := fun z hz ↦ by
    have := hK.isOpen_compl.inter_closure ⟨hz.2, hz.1⟩
    rwa [inter_comm] at this
  exact Set.EqOn.of_subset_closure (s := s ∩ Kᶜ) (t := closure s ∩ Kᶜ) (f := φ) (g := 0)
    (fun z hz ↦ h z hz.1 hz.2) (hφ.mono inter_subset_left) continuousOn_const
    (inter_subset_inter_left _ subset_closure) hsub ⟨hy, hyK⟩

/-- The indicator on `tsupport f` of a function `φ` continuous on `closure s` and vanishing on
`s \ tsupport f` is continuous on `closure s'`, when `s ∩ V = s' ∩ V` for an open `V ⊇ tsupport f`:
near a point of `V`, `closure s' ∩ V ⊆ closure s` and `φ` serves; away from `V` the indicator
vanishes on a neighbourhood. The continuity clauses of
`ContDiffOnClosure.congr_set_of_tsupport_subset`. -/
theorem ContinuousOn.indicator_tsupport_of_inter_eq {Y : Type*} [TopologicalSpace Y]
    {f : Y → F} {s s' V : Set Y} (hV : IsOpen V) (hsV : s ∩ V = s' ∩ V) (hsupp : tsupport f ⊆ V)
    {φ : Y → G} (hφ : ContinuousOn φ (closure s)) (hφ0 : ∀ x ∈ s, x ∉ tsupport f → φ x = 0) :
    ContinuousOn ((tsupport f).indicator φ) (closure s') := by
  -- `closure s' ∩ V ⊆ closure s`, and `closure s` is a neighbourhood within `closure s'` there
  have hcl : closure s' ∩ V ⊆ closure s := fun x hx ↦ by
    have h1 : x ∈ closure (s' ∩ V) := by
      have := hV.inter_closure ⟨hx.2, hx.1⟩
      rwa [inter_comm] at this
    rw [← hsV] at h1
    exact closure_mono inter_subset_left h1
  have hnhds : ∀ x ∈ closure s', x ∈ V → closure s ∈ 𝓝[closure s'] x := fun x hx hxV ↦
    mem_nhdsWithin.2 ⟨V, hV, hxV, fun z hz ↦ hcl ⟨hz.2, hz.1⟩⟩
  intro x hx
  have heq : ∀ z ∈ closure s, (tsupport f).indicator φ z = φ z := fun z hz ↦ by
    by_cases hzK : z ∈ tsupport f
    · exact indicator_of_mem hzK _
    · rw [indicator_of_notMem hzK,
        hφ.eq_zero_of_notMem_of_forall (isClosed_tsupport f) hφ0 hz hzK]
  by_cases hxV : x ∈ V
  · have h1 : ContinuousWithinAt φ (closure s') x :=
      (hφ x (hcl ⟨hx, hxV⟩)).mono_of_mem_nhdsWithin (hnhds x hx hxV)
    refine h1.congr_of_eventuallyEq ?_ (heq x (hcl ⟨hx, hxV⟩))
    filter_upwards [hnhds x hx hxV] with z hz using heq z hz
  · have hxs : x ∉ tsupport f := fun h ↦ hxV (hsupp h)
    have hev : (tsupport f).indicator φ =ᶠ[𝓝 x] fun _ ↦ 0 := by
      filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hxs] with z hz
      exact indicator_of_notMem hz _
    exact (continuousAt_const.congr hev.symm).continuousWithinAt

/-- **The class `C¹(Ω̄)` is local on the support**: for open sets `s`, `V` and a set `s'` with
`s ∩ V = s' ∩ V`, a function `f ∈ C¹(s̄)` with `tsupport f ⊆ V` is in `C¹(s̄')`. Near a point of
`V`, `closure s' ∩ V ⊆ closure (s ∩ V)` and the data of `f` on `closure s` serve; away from `V`
the function vanishes on a neighbourhood. The extension of `Df` to `closure s'` is
`(tsupport f).indicator` of the given extension, which vanishes on `closure s \ tsupport f`
(`ContinuousOn.eq_zero_of_notMem_of_forall`, `ContinuousOn.indicator_tsupport_of_inter_eq`).
Used to move a field supported in a chart ball from `Ω` to the global rotated epigraph. -/
theorem ContDiffOnClosure.congr_set_of_tsupport_subset {s' V : Set X} (hs : IsOpen s)
    (hV : IsOpen V) (hsV : s ∩ V = s' ∩ V) (hsupp : tsupport f ⊆ V)
    (hf₀ : ContinuousOn f (closure s)) (hf₁ : ContDiffOnClosure 𝕜 1 f s) :
    ContinuousOn f (closure s') ∧ ContDiffOnClosure 𝕜 1 f s' := by
  have hmem : ∀ x ∈ s', x ∈ V → x ∈ s := fun x hx hxV ↦ by
    have : x ∈ s' ∩ V := ⟨hx, hxV⟩
    rw [← hsV] at this
    exact this.1
  have hcontf : ContinuousOn f (closure s') := by
    have := hf₀.indicator_tsupport_of_inter_eq hV hsV hsupp
      fun x _ hx ↦ image_eq_zero_of_notMem_tsupport (f := f) hx
    rwa [Set.indicator_eq_self.2 (subset_tsupport f)] at this
  refine ⟨hcontf, ?_⟩
  rw [contDiffOnClosure_one_iff] at hf₁ ⊢
  obtain ⟨hf, -, ⟨g₁, hg₁c, hg₁e⟩⟩ := hf₁
  refine ⟨fun x hx ↦ ?_, ⟨f, hcontf, fun _ _ ↦ rfl⟩, ⟨(tsupport f).indicator g₁,
    hg₁c.indicator_tsupport_of_inter_eq hV hsV hsupp fun x hx hxK ↦ ?_, fun x hx ↦ ?_⟩⟩
  · by_cases hxV : x ∈ V
    · exact (hf.contDiffAt (hs.mem_nhds (hmem x hx hxV))).contDiffWithinAt
    · have hxs : x ∉ tsupport f := fun h ↦ hxV (hsupp h)
      exact (contDiffAt_const.congr_of_eventuallyEq
        (notMem_tsupport_iff_eventuallyEq.1 hxs)).contDiffWithinAt
  · rw [hg₁e hx]
    exact fderiv_of_notMem_tsupport 𝕜 hxK
  · by_cases hxK : x ∈ tsupport f
    · rw [indicator_of_mem hxK, hg₁e (hmem x hx (hsupp hxK))]
    · rw [indicator_of_notMem hxK, fderiv_of_notMem_tsupport 𝕜 hxK]

/-- **`C¹(s̄)` is stable under conjugation by an affine bijection and a linear map**: for `s` open
and `f ∈ C¹(s̄)`, the field `x ↦ L (f (M x + b))` is of class `C¹` up to the boundary on the
preimage of `s` under `x ↦ M x + b`. -/
theorem ContDiffOnClosure.clm_comp_comp_affine {Y : Type*} [NormedAddCommGroup Y]
    [NormedSpace 𝕜 Y] (hs : IsOpen s) (hf : ContDiffOnClosure 𝕜 1 f s) (L : F →L[𝕜] G)
    (M : Y ≃L[𝕜] X) (b : X) :
    ContDiffOnClosure 𝕜 1 (fun y ↦ L (f (M y + b))) ((fun y ↦ M y + b) ⁻¹' s) := by
  obtain ⟨hcd, ⟨g, hgc, hge⟩, ⟨g', hg'c, hg'e⟩⟩ := contDiffOnClosure_one_iff.1 hf
  have hΦ : Continuous fun y ↦ M y + b := M.continuous.add continuous_const
  have hΦh : (fun y ↦ M y + b) = M.toHomeomorph.trans (Homeomorph.addRight b) := by
    funext y; rfl
  have hcl : closure ((fun y ↦ M y + b) ⁻¹' s) = (fun y ↦ M y + b) ⁻¹' closure s := by
    rw [hΦh, Homeomorph.preimage_closure]
  refine contDiffOnClosure_one_iff.2 ⟨?_, ⟨fun y ↦ L (g (M y + b)), ?_, fun y hy ↦ ?_⟩,
    ⟨fun y ↦ (L.comp (g' (M y + b))).comp (M : Y →L[𝕜] X), ?_, fun y hy ↦ ?_⟩⟩
  · exact L.contDiff.comp_contDiffOn
      (hcd.comp (M.contDiff.add contDiff_const).contDiffOn (mapsTo_preimage _ _))
  · rw [hcl]
    exact L.continuous.comp_continuousOn (hgc.comp hΦ.continuousOn (mapsTo_preimage _ _))
  · simp only [hge hy]
  · rw [hcl]
    exact (continuousOn_const.clm_comp (hg'c.comp hΦ.continuousOn
      (mapsTo_preimage _ _))).clm_comp continuousOn_const
  · have hd : DifferentiableAt 𝕜 f (M y + b) :=
      (hcd.differentiableOn one_ne_zero).differentiableAt (hs.mem_nhds hy)
    simp only [hg'e hy]
    exact (L.hasFDerivAt.comp y (hd.hasFDerivAt.comp y (M.hasFDerivAt.add_const b))).fderiv.symm

end One

section Real

variable {E E' F' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [NormedAddCommGroup F'] [NormedSpace ℝ F']

/-- **A function of class `C¹(s̄)` on a bounded set has a bounded derivative on `s`**: the real
case of `ContDiffOnClosure.exists_norm_fderiv_le`. -/
theorem ContDiffOnClosure.exists_norm_fderiv_le_of_isBounded [ProperSpace E] {f : E → F'}
    {s : Set E} (hf : ContDiffOnClosure ℝ 1 f s) (hs : Bornology.IsBounded s) :
    ∃ M, ∀ x ∈ s, ‖fderiv ℝ f x‖ ≤ M :=
  hf.exists_norm_fderiv_le hs

/-- **`C¹(s̄)` is stable under a rigid motion on the right**: `f ∘ T ∈ C¹(T⁻¹(s)‾)` for
`f ∈ C¹(s̄)`, `s` open. The extensions compose with `T`, the derivative with `T`'s linear part. -/
theorem ContDiffOnClosure.comp_affineIsometryEquiv {f : E → F'} {s : Set E} (hs : IsOpen s)
    (hf : ContDiffOnClosure ℝ 1 f s) (T : E' ≃ᵃⁱ[ℝ] E) :
    ContDiffOnClosure ℝ 1 (fun z ↦ f (T z)) (T ⁻¹' s) := by
  rw [contDiffOnClosure_one_iff] at hf ⊢
  obtain ⟨hf, ⟨g₀, hg₀c, hg₀e⟩, ⟨g₁, hg₁c, hg₁e⟩⟩ := hf
  have hcl : closure (T ⁻¹' s) = T ⁻¹' closure s := by
    have := T.toHomeomorph.preimage_closure s
    rwa [AffineIsometryEquiv.coe_toHomeomorph, eq_comm] at this
  have hTc : ContinuousOn T (closure (T ⁻¹' s)) := T.continuous.continuousOn
  have hmaps : MapsTo T (closure (T ⁻¹' s)) (closure s) := fun z hz ↦ by rwa [hcl] at hz
  have hT : ContDiff ℝ 1 T := T.toAffineIsometry.toContinuousAffineMap.contDiff
  refine ⟨hf.comp hT.contDiffOn (mapsTo_preimage T s), ⟨fun z ↦ g₀ (T z), hg₀c.comp hTc hmaps,
    fun z hz ↦ hg₀e hz⟩, ⟨fun z ↦ (g₁ (T z)).comp
      (T.linearIsometryEquiv.toContinuousLinearEquiv : E' →L[ℝ] E),
    (hg₁c.comp hTc hmaps).clm_comp continuousOn_const, fun z hz ↦ ?_⟩⟩
  have hd : DifferentiableAt ℝ f (T z) :=
    (hf.differentiableOn one_ne_zero).differentiableAt (hs.mem_nhds hz)
  simp only [hg₁e hz]
  exact (hd.hasFDerivAt.comp z (T.hasFDerivAt z)).fderiv.symm

end Real
