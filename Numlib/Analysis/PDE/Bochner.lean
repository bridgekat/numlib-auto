import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Vector-valued functions of time: the classes `C^k(s; V)` and `L^p(s; V)` read in a larger space

The evolution equations of Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, chapter 10, describe their solutions as curves `u : [0, ∞) → H` in a Hilbert space
`H = L²(Ω)`, and write beside `u ∈ C([0,∞); H)` — which is Mathlib's `ContinuousOn` — the
membership of a *smaller* space: `u ∈ C((0,∞); H²(Ω) ∩ H¹₀(Ω))`, `u ∈ C¹([0,∞); H¹₀(Ω))`,
`u ∈ L²(0,∞; H¹₀(Ω))`. In this library the smaller spaces are separate types, mapped into the
larger one by a continuous linear injection `J : V →L[ℝ] W`. Each such clause is then "`u`
factors through `J` by a curve of the required regularity":

* `Bochner.ContDiffOnThrough J k u s`: there is `v : ℝ → V` of class `C^k` on `s` with
  `u = J ∘ v` on `s` — the class `C^k(s; V)` of a curve whose values are read in `W`;
* `Bochner.MemLpThrough J p u s`: there is `v ∈ L^p(s; V)` (Mathlib's `MemLp` of a `V`-valued
  function of a real variable, which is the Bochner `L^p` space) with `u = J ∘ v` on `s`.

The module needs only Mathlib: the predicates are stated for an arbitrary continuous linear `J`,
and the two lemmas that carry weight are `ContDiffOnThrough.derivWithin_eq` — the derivative of
the curve is the image of the derivative of the lift, `d/dt (J v) = J (dv/dt)`, the step "`A ∈
L(H₁, H)` and `u ∈ C([0,∞); H₁)` give `d/dt (A u) = A (du/dt)`" of Brezis's proof of Theorem 7.5
— and `MemLpThrough.of_contDiffOnThrough_of_integrable`, the form in which the energy
identities of the heat equation deliver `u ∈ L²(0,∞; H¹₀(Ω))`.

No `L²(0,T; V)` type is built and no jointly measurable representative of a curve is
constructed; the space–time reading of a curve of Sobolev functions, `u(x, t)`, is a separate
module.

## Main definitions

* `Bochner.ContDiffOnThrough J k u s`, the class `C^k(s; V)`;
* `Bochner.MemLpThrough J p u s`, the class `L^p(s; V)`.

## Main statements

* `Bochner.ContDiffOnThrough.contDiffOn`, `.mono`, `.of_le`, `.comp`, `.of_comp`: the curve itself
  is `C^k`, monotonicity in the set and the order, composition with a further bounded map and
  restriction of the lift; `.infty_of_forall_nat`: through an injective `J`, `C^n(s; V)` for
  every `n : ℕ` is `C^∞(s; V)`;
* `Bochner.ContDiffOnThrough.derivWithin_eq`, `.derivWithin`: the derivative commutes with the
  embedding, and is again of class `C^m(s; V)` for `m + 1 ≤ k`;
* `Bochner.MemLpThrough.of_contDiffOnThrough_of_integrable`: a continuous lift whose norm to the
  power `p` is integrable gives `L^p(s; V)`.

## References

[brezis2011functional], §10.1, the notation `C([0,∞); H)`, `L²(0,∞; H¹₀(Ω))`, and the proof of
Theorem 7.5.
-/

open MeasureTheory Set

open scoped ENNReal Topology

namespace Bochner

variable {V W X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W] [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ### The class `C^k(s; V)` -/

/-- **The class `C^k(s; V)` of a curve read in `W`**: `u : ℝ → W` factors on `s` through the
continuous linear `J : V →L[ℝ] W` by a curve `v : ℝ → V` of class `C^k` on `s`. With `k = 0`
this is `C(s; V)`. -/
def ContDiffOnThrough (J : V →L[ℝ] W) (k : WithTop ℕ∞) (u : ℝ → W) (s : Set ℝ) : Prop :=
  ∃ v : ℝ → V, ContDiffOn ℝ k v s ∧ ∀ t ∈ s, u t = J (v t)

namespace ContDiffOnThrough

variable {J : V →L[ℝ] W} {k : WithTop ℕ∞} {u : ℝ → W} {s : Set ℝ}

/-- A curve of class `C^k(s; V)` is a `C^k` curve in `W`. -/
theorem contDiffOn (h : ContDiffOnThrough J k u s) : ContDiffOn ℝ k u s := by
  obtain ⟨v, hv, huv⟩ := h
  exact (J.contDiff.comp_contDiffOn hv).congr fun t ht ↦ huv t ht

theorem continuousOn (h : ContDiffOnThrough J k u s) : ContinuousOn u s :=
  h.contDiffOn.continuousOn

/-- Monotonicity in the set. -/
theorem mono {s' : Set ℝ} (h : ContDiffOnThrough J k u s) (hs : s' ⊆ s) :
    ContDiffOnThrough J k u s' :=
  let ⟨v, hv, huv⟩ := h
  ⟨v, hv.mono hs, fun t ht ↦ huv t (hs ht)⟩

/-- Monotonicity in the order. -/
theorem of_le {k' : WithTop ℕ∞} (h : ContDiffOnThrough J k u s) (hk : k' ≤ k) :
    ContDiffOnThrough J k' u s :=
  let ⟨v, hv, huv⟩ := h
  ⟨v, hv.of_le hk, huv⟩

/-- **One lift for all orders**: a curve of class `C^n(s; V)` for every `n : ℕ`, through an
injective `J`, is of class `C^∞(s; V)`: the lifts at the various orders agree on `s`, so the
lift of order `0` is of every class. -/
theorem infty_of_forall_nat (hJ : Function.Injective J)
    (h : ∀ n : ℕ, ContDiffOnThrough J n u s) : ContDiffOnThrough J (⊤ : ℕ∞) u s := by
  obtain ⟨v, -, huv⟩ := h 0
  refine ⟨v, contDiffOn_infty.2 fun n ↦ ?_, huv⟩
  obtain ⟨w, hw, huw⟩ := h n
  exact hw.congr fun t ht ↦ hJ ((huv t ht).symm.trans (huw t ht))

/-- A `C^k` curve in `V` is of class `C^k(s; V)` through the identity. -/
theorem of_contDiffOn {v : ℝ → V} (hv : ContDiffOn ℝ k v s) :
    ContDiffOnThrough (ContinuousLinearMap.id ℝ V) k v s :=
  ⟨v, hv, fun _ _ ↦ rfl⟩

/-- Through the identity, the class `C^k(s; V)` is Mathlib's `ContDiffOn`. -/
theorem id_iff {v : ℝ → V} :
    ContDiffOnThrough (ContinuousLinearMap.id ℝ V) k v s ↔ ContDiffOn ℝ k v s :=
  ⟨contDiffOn, of_contDiffOn⟩

/-- Composition with a further bounded map. -/
theorem comp (h : ContDiffOnThrough J k u s) (J' : W →L[ℝ] X) :
    ContDiffOnThrough (J'.comp J) k (J' ∘ u) s :=
  let ⟨v, hv, huv⟩ := h
  ⟨v, hv, fun t ht ↦ by simp [huv t ht]⟩

/-- Restriction of the lift along a factorization of the embedding: a curve of class
`C^k(s; V₁)` read in `W` through `J₂ ∘ J₁` is of class `C^k(s; V₂)` through `J₂`. This is how
`C^k(s; H²(Ω))` implies `C^k(s; H¹(Ω))`. -/
theorem of_comp {V₁ : Type*} [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] {J₁ : V₁ →L[ℝ] V}
    (h : ContDiffOnThrough (J.comp J₁) k u s) : ContDiffOnThrough J k u s :=
  let ⟨v, hv, huv⟩ := h
  ⟨J₁ ∘ v, J₁.contDiff.comp_contDiffOn hv, fun t ht ↦ by simpa using huv t ht⟩

/-- **The derivative commutes with the embedding**: if `u = J ∘ v` on `s` with `v` of class
`C^k`, `1 ≤ k`, then at every point of a uniquely differentiable `s`,
`derivWithin u s t = J (derivWithin v s t)`. -/
theorem derivWithin_eq {v : ℝ → V} (hv : ContDiffOn ℝ k v s) (huv : ∀ t ∈ s, u t = J (v t))
    (hk : 1 ≤ k) (hs : UniqueDiffOn ℝ s) {t : ℝ} (ht : t ∈ s) :
    derivWithin u s t = J (derivWithin v s t) := by
  have hd : HasDerivWithinAt v (derivWithin v s t) s t :=
    ((hv.differentiableOn (ENat.one_le_iff_ne_zero_withTop.1 hk)) t ht).hasDerivWithinAt
  have := (HasFDerivAt.comp_hasDerivWithinAt t (J.hasFDerivAt (x := v t)) hd).congr
    (fun x hx ↦ huv x hx) (huv t ht)
  exact this.derivWithin (hs t ht)

/-- The derivative of a curve of class `C^k(s; V)` is of class `C^m(s; V)` for `m + 1 ≤ k`, its
lift being the derivative of the lift. -/
theorem derivWithin {m : WithTop ℕ∞} (h : ContDiffOnThrough J k u s) (hs : UniqueDiffOn ℝ s)
    (hmk : m + 1 ≤ k) : ContDiffOnThrough J m (derivWithin u s) s :=
  let ⟨v, hv, huv⟩ := h
  ⟨_root_.derivWithin v s, hv.derivWithin hs hmk, fun t ht ↦
    derivWithin_eq hv huv (le_trans (by simp) hmk) hs ht⟩

end ContDiffOnThrough

/-! ### The class `L^p(s; V)` -/

/-- **The class `L^p(s; V)` of a curve read in `W`**: `u : ℝ → W` agrees on `s` with `J ∘ v` for
a `v : ℝ → V` in the Bochner space `L^p(s; V)`, Mathlib's `MemLp v p (volume.restrict s)`.
Pointwise agreement on `s` is asked rather than agreement almost everywhere, because every
consumer's curve is continuous. -/
def MemLpThrough (J : V →L[ℝ] W) (p : ℝ≥0∞) (u : ℝ → W) (s : Set ℝ) : Prop :=
  ∃ v : ℝ → V, MemLp v p (volume.restrict s) ∧ ∀ t ∈ s, u t = J (v t)

namespace MemLpThrough

variable {J : V →L[ℝ] W} {p : ℝ≥0∞} {u : ℝ → W} {s : Set ℝ}

/-- A curve of class `L^p(s; V)` is in `L^p(s; W)`. -/
theorem memLp (hs : MeasurableSet s) (h : MemLpThrough J p u s) : MemLp u p (volume.restrict s) :=
  let ⟨_, hv, huv⟩ := h
  (hv.continuousLinearMap_comp J).ae_eq
    ((ae_restrict_iff' hs).2 (Filter.Eventually.of_forall fun t ht ↦ (huv t ht).symm))

/-- Monotonicity in the set. -/
theorem mono {s' : Set ℝ} (h : MemLpThrough J p u s) (hs : s' ⊆ s) : MemLpThrough J p u s' :=
  let ⟨v, hv, huv⟩ := h
  ⟨v, hv.mono_measure (Measure.restrict_mono hs le_rfl), fun t ht ↦ huv t (hs ht)⟩

/-- Composition with a further bounded map. -/
theorem comp (h : MemLpThrough J p u s) (J' : W →L[ℝ] X) : MemLpThrough (J'.comp J) p (J' ∘ u) s :=
  let ⟨v, hv, huv⟩ := h
  ⟨v, hv, fun t ht ↦ by simp [huv t ht]⟩

/-- Restriction of the lift along a factorization of the embedding. -/
theorem of_comp {V₁ : Type*} [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] {J₁ : V₁ →L[ℝ] V}
    (h : MemLpThrough (J.comp J₁) p u s) : MemLpThrough J p u s :=
  let ⟨v, hv, huv⟩ := h
  ⟨J₁ ∘ v, hv.continuousLinearMap_comp J₁, fun t ht ↦ by simpa using huv t ht⟩

/-- **From continuity and an integral bound to `L^p(s; V)`**: a curve that factors on the
measurable `s` through `J` by a continuous `v` with `∫_s ‖v t‖^p dt < ∞`, `0 < p < ∞`, is of class
`L^p(s; V)`. This is the form in which the energy identities of the heat equation deliver
`u ∈ L²(0,∞; H¹₀(Ω))`: continuity into `H¹₀` plus `∫₀^∞ ‖u(t)‖²_{H¹} dt < ∞`. -/
theorem of_contDiffOnThrough_of_integrable {v : ℝ → V} (hv : ContinuousOn v s)
    (huv : ∀ t ∈ s, u t = J (v t)) (hs : MeasurableSet s) (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (hint : IntegrableOn (fun t ↦ ‖v t‖ ^ p.toReal) s) : MemLpThrough J p u s := by
  refine ⟨v, ?_, huv⟩
  have hmeas : AEStronglyMeasurable v (volume.restrict s) := hv.aestronglyMeasurable hs
  have := (memLp_norm_rpow_iff (p := p) (q := p) (μ := volume.restrict s) hmeas hp0 hp).1
  rw [ENNReal.div_self hp0 hp, memLp_one_iff_integrable] at this
  exact this hint

end MemLpThrough

end Bochner
