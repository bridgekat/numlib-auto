/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Calculus.ContDiff.Defs`, beside `ContDiffOn`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs

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
  open `s`.

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
