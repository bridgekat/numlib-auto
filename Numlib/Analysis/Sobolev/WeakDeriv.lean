/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.WeakDeriv`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.TestFunction

/-!
# Weak derivatives on an open set

A function `w : E → E [×n]→L[ℝ] F` is an *`n`-th weak derivative* of `f : E → F` on an open set
`Ω ⊆ E` when the integration by parts formula

`∫_Ω (∂^n φ x) y • f x dx = (-1)^n ∫_Ω φ x • (w x) y dx`

holds for every test function `φ ∈ C_0^∞(Ω)` and every tuple `y` of `n` directions, both `f` and
`w` being locally integrable on `Ω`. This is `HasWeakIteratedFDerivOn`, the definition of
Atkinson and Han, *Theoretical Numerical Analysis: A Functional Analysis Framework*, 3rd edition,
Definition 7.1.3, read for all multi-indices of a fixed length at once: a tuple `y : Fin n → E` of
directions plays the role of a multi-index `α` with `|α| = n`, and quantifying over all tuples is
quantifying over all multi-indices of that length.

## Main definitions

* `MeasureTheory.LocallyMemLpOn f p s μ`, the space `L^p_loc(s)` of functions that are
  `p`-integrable near every point of `s` (Atkinson–Han, Definition 7.1.1); for `p = 1` this is
  Mathlib's `MeasureTheory.LocallyIntegrableOn`, by `MeasureTheory.locallyMemLpOn_one_iff`.
* `HasWeakIteratedFDerivOn n f w Ω μ`, the weak derivative of order `n` (Atkinson–Han,
  Definition 7.1.3), and `HasWeakFDerivOn f w Ω μ`, its first-order form with `w` valued in
  `E →L[ℝ] F`.
* `HasWeakIteratedLineDerivOn y f w Ω μ`, the same definition read for the *single* tuple `y` of
  directions, so with `w` valued in `F`: this is Atkinson–Han, Definition 7.1.3, for one
  multi-index `α`, where `HasWeakIteratedFDerivOn` is it for all `α` of a given length at once
  (`HasWeakIteratedFDerivOn.lineDeriv`).

## Main statements

* `HasWeakIteratedFDerivOn.ae_eq` and `HasWeakIteratedLineDerivOn.ae_eq`: a weak derivative is
  unique almost everywhere on `Ω`
  (Atkinson–Han, Lemma 7.1.4). The proof is Mathlib's generalized variational lemma
  `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` (Atkinson–Han, Lemma 7.1.2) applied to the
  difference of two weak derivatives.
* `ContDiffOn.hasWeakIteratedFDerivOn`: a classical derivative of a `C^N` function on `Ω` is also
  its weak derivative, for every order `n ≤ N` (Atkinson–Han, Lemma 7.1.5); so the weak derivative
  extends the classical one.
* `HasWeakIteratedFDerivOn.add`, `.const_smul`, `.neg`, `.sub`, `.zero`: weak differentiation is
  linear (Atkinson–Han, Proposition 7.1.10).
* `HasWeakIteratedLineDerivOn.mul_contDiff`: the Leibniz rule for a *smooth* factor, at first
  order (the smooth-factor case of Atkinson–Han, Proposition 7.1.11). Nothing is mollified: the
  product of a test function with a smooth function is again a test function
  (`TestFunction.mulContDiff`), so the identity is a direct integration by parts. The general
  Leibniz rule, with both factors merely locally integrable, is not here.
* `HasWeakIteratedFDerivOn.mono` and `HasWeakIteratedLineDerivOn.mono`: a weak derivative on `Ω`
  is a weak derivative on every smaller open set.
* `HasWeakIteratedLineDerivOn.comp_continuousLinearMap`: a continuous linear map passes through
  the weak derivative, and `HasWeakIteratedLineDerivOn.ofReal_iff`, its consequence that a real
  function has a real weak derivative exactly when its complexification has the complexified one.
* `MeasureTheory.LocallyMemLpOn.memLp_restrict_of_isCompact`: a function locally in `L^p` on `s`
  is in `L^p` of every compact subset of `s`, for `p < ∞`; the `L^p` analogue of Mathlib's
  `MeasureTheory.LocallyIntegrableOn.integrableOn_compact_subset`.
* `ContDiff.iteratedFDeriv_congr_perm`: **the iterated derivative of a `C^∞` function is symmetric
  in its arguments**, which Mathlib has only at order two (`ContDiffAt.isSymmSndFDerivAt`) or, at
  every order, for analytic functions. The vehicle is `listFDeriv`, differentiation along the
  entries of a *list* of directions, along which the commutation of two directional derivatives
  propagates by an induction on `List.Perm`.

## Implementation notes

Mathlib's `Mathlib/Analysis/Distribution/Sobolev.lean` is about the Bessel potential spaces
`H^{s,p}` of tempered distributions on the *whole* space, which is a different subject: nothing
there concerns a domain, and in particular there is no weak derivative on an open set.

This file is a stand-in for work that is on its way into Mathlib: Mathlib PR 32305 and its
continuation `grunweg/SobolevSlobodeckij` (Michael Rothgang, Filippo Nuccio and Floris van Doorn)
develop weak derivatives, `W^{k,p}(Ω)` and the Sobolev–Slobodeckij spaces in far greater depth.
That development pins an older Lean toolchain and cannot be imported here, so the names and the
argument order below follow it where possible — `Ω : TopologicalSpace.Opens E` and a trailing
measure argument, `MemSobolev f k p Ω μ` in the companion file — in order that a later migration
be a rename rather than a rewrite. Two deliberate differences:

* there the weak derivative is a *distribution*, an element of `𝓓'(Ω, E →L[ℝ] F)`, obtained from a
  weak Taylor series through `FormalMultilinearSeries`; here it is a predicate relating two
  functions, which is lighter and is all that the integration by parts formula needs;
* the order is carried by an explicit `n` and the derivative is `ContinuousMultilinearMap`-valued,
  so that all derivatives of order `n` are described by a single object without iterating the
  construction.

`HasWeakIteratedLineDerivOn` moves back the other way, towards the classical indexing by
multi-indices: it fixes the tuple of directions and so is `F`-valued. It is what
`Numlib/Analysis/Sobolev/MultiIndex.lean` needs, because the norm of Atkinson–Han's
Definition 7.2.2 sums over the multi-indices `α` separately and not over the orders `|α|`, and
that norm is the one an inner product induces when `p = 2`. Nothing is lost by keeping both: the
tuple-by-tuple form is one field of the tensor form, `HasWeakIteratedFDerivOn.lineDeriv`.

The `n`-th derivative of the *test* function is what is differentiated in the definition, and
`ContDiff.fderiv_iteratedFDeriv_apply` — the statement that for a smooth function an extra
directional derivative may be taken either inside or outside the `n` iterated ones — is what makes
the two sides of the integration by parts formula carry the *same* tuple `y`. Without it the
formula would relate `∂^n φ (y)` to `∂^n f (y ∘ Fin.rev)`, since integrating by parts `n` times
moves the derivatives onto `f` in the opposite order.
-/

open Filter MeasureTheory Set TopologicalSpace

open scoped ContDiff Distributions ENNReal Topology

/-! ### Locally `p`-integrable functions -/

namespace MeasureTheory

variable {X G : Type*} [TopologicalSpace X] [MeasurableSpace X] [NormedAddCommGroup G]
  {f : X → G} {s t : Set X} {μ : Measure X} {p : ℝ≥0∞}

/-- A function is *locally `p`-integrable on `s`*, written `f ∈ L^p_loc(s)`, when every point of
`s` has a neighbourhood within `s` on which `f` is `p`-integrable. For `p = 1` this is
`MeasureTheory.LocallyIntegrableOn`, by `MeasureTheory.locallyMemLpOn_one_iff`. -/
def LocallyMemLpOn (f : X → G) (p : ℝ≥0∞) (s : Set X) (μ : Measure X := by volume_tac) : Prop :=
  ∀ x ∈ s, ∃ u ∈ 𝓝[s] x, MemLp f p (μ.restrict u)

/-- Local `1`-integrability is local integrability. -/
theorem locallyMemLpOn_one_iff : LocallyMemLpOn f 1 s μ ↔ LocallyIntegrableOn f s μ := by
  simp only [LocallyMemLpOn, LocallyIntegrableOn, IntegrableAtFilter, IntegrableOn,
    memLp_one_iff_integrable]

alias ⟨LocallyMemLpOn.locallyIntegrableOn, LocallyIntegrableOn.locallyMemLpOn⟩ :=
  locallyMemLpOn_one_iff

omit [TopologicalSpace X] in
/-- `L^p` membership is stable under a union of two sets, for `p < ∞`. The exponent `p = ∞` is
excluded only because the proof compares `p`-th powers of the `L^p` norms; the statement is true
there too. -/
theorem MemLp.union_of_ne_top (hp : p ≠ ⊤) (hs : MemLp f p (μ.restrict s))
    (ht : MemLp f p (μ.restrict t)) : MemLp f p (μ.restrict (s ∪ t)) := by
  refine ⟨aestronglyMeasurable_union_iff.2 ⟨hs.1, ht.1⟩, ?_⟩
  rcases eq_or_ne p 0 with rfl | hp0
  · simp
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hrw : ∀ ν : Measure X, eLpNorm f p ν ^ p.toReal = ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂ν := fun ν ↦ by
    rw [eLpNorm_eq_eLpNorm' hp0 hp, lintegral_rpow_enorm_eq_rpow_eLpNorm' hr]
  have key : eLpNorm f p (μ.restrict (s ∪ t)) ^ p.toReal
      ≤ eLpNorm f p (μ.restrict s) ^ p.toReal + eLpNorm f p (μ.restrict t) ^ p.toReal := by
    rw [hrw, hrw, hrw]
    exact lintegral_union_le _ _ _
  have hfin : eLpNorm f p (μ.restrict (s ∪ t)) ^ p.toReal ≠ ⊤ :=
    (key.trans_lt (ENNReal.add_lt_top.2
      ⟨ENNReal.rpow_lt_top_of_nonneg hr.le hs.2.ne,
        ENNReal.rpow_lt_top_of_nonneg hr.le ht.2.ne⟩)).ne
  rw [lt_top_iff_ne_top]
  intro hcon
  rw [hcon, ENNReal.top_rpow_of_pos hr] at hfin
  exact hfin rfl

/-- Local `L^p` membership passes to subsets. -/
theorem LocallyMemLpOn.mono_set (hf : LocallyMemLpOn f p s μ) (hts : t ⊆ s) :
    LocallyMemLpOn f p t μ := fun x hx ↦
  let ⟨u, hu, h⟩ := hf x (hts hx); ⟨u, nhdsWithin_mono x hts hu, h⟩

/-- **A function locally in `L^p` on `s` is in `L^p` of every compact subset of `s`**, for
`p < ∞`. This is the `L^p` analogue of
`MeasureTheory.LocallyIntegrableOn.integrableOn_compact_subset`, and is proved the same way, by
`IsCompact.induction_on`. -/
theorem LocallyMemLpOn.memLp_restrict_of_isCompact (hf : LocallyMemLpOn f p s μ) (hp : p ≠ ⊤)
    (hs : IsCompact s) : MemLp f p (μ.restrict s) :=
  IsCompact.induction_on hs (by simp)
    (fun _ _ hst ht ↦ ht.mono_measure (Measure.restrict_mono hst le_rfl))
    (fun _ _ h₁ h₂ ↦ MemLp.union_of_ne_top hp h₁ h₂) hf

/-- **A function locally in `L^p` on `s` is in `L^p` of every compact subset of `s`**, for
`p < ∞`. -/
theorem LocallyMemLpOn.memLp_restrict_of_compact_subset (hf : LocallyMemLpOn f p s μ)
    (hp : p ≠ ⊤)
    (hts : t ⊆ s) (ht : IsCompact t) : MemLp f p (μ.restrict t) :=
  (hf.mono_set hts).memLp_restrict_of_isCompact hp ht

/-- If `f` is locally integrable on `s` and `g` is continuous with compact support inside `s`,
then `g • f` is integrable on the whole space. This is the version on a set of Mathlib's
`MeasureTheory.LocallyIntegrable.integrable_smul_left_of_hasCompactSupport`. -/
theorem LocallyIntegrableOn.integrable_smul_left_of_tsupport_subset [OpensMeasurableSpace X]
    [T2Space X] [NormedSpace ℝ G] (hf : LocallyIntegrableOn f s μ) {g : X → ℝ}
    (hg : Continuous g) (h'g : HasCompactSupport g) (hgs : tsupport g ⊆ s) :
    Integrable (fun x ↦ g x • f x) μ := by
  have hK : IsCompact (tsupport g) := h'g
  have h1 : (fun x ↦ g x • f x) = (tsupport g).indicator fun x ↦ g x • f x :=
    (indicator_eq_self.2 (Function.support_subset_iff'.2 fun x hx ↦ by
      simp [image_eq_zero_of_notMem_tsupport hx])).symm
  rw [h1, Set.indicator_smul]
  exact Integrable.smul_of_top_right
    ((integrable_indicator_iff hK.measurableSet).2 (hf.integrableOn_compact_subset hgs hK))
    (hg.memLp_top_of_hasCompactSupport h'g μ)

/-- The product of a locally integrable real function with a continuous one is locally
integrable: near each point the continuous factor is bounded. -/
theorem LocallyIntegrableOn.mul_continuous [OpensMeasurableSpace X] {f g : X → ℝ}
    (hf : LocallyIntegrableOn f s μ)
    (hg : Continuous g) : LocallyIntegrableOn (fun x ↦ f x * g x) s μ := by
  intro x hx
  obtain ⟨u, hu, hfu⟩ := hf x hx
  have hSopen : IsOpen {y | ‖g y‖ < ‖g x‖ + 1} := isOpen_lt hg.norm continuous_const
  have hxS : x ∈ {y | ‖g y‖ < ‖g x‖ + 1} := by simp
  refine ⟨u ∩ {y | ‖g y‖ < ‖g x‖ + 1},
    Filter.inter_mem hu (mem_nhdsWithin_of_mem_nhds (hSopen.mem_nhds hxS)), ?_⟩
  refine Integrable.mul_bdd (c := ‖g x‖ + 1) (hfu.mono_set inter_subset_left)
    hg.aestronglyMeasurable.restrict ?_
  exact ((ae_restrict_mem hSopen.measurableSet).mono fun y hy ↦ hy.le).filter_mono
    (ae_mono (Measure.restrict_mono inter_subset_right le_rfl))

/-- Composing a locally integrable function with a continuous linear map keeps it locally
integrable. -/
theorem LocallyIntegrableOn.comp_continuousLinearMap {G' : Type*} [NormedAddCommGroup G']
    [NormedSpace ℝ G] [NormedSpace ℝ G'] (hf : LocallyIntegrableOn f s μ) (L : G →L[ℝ] G') :
    LocallyIntegrableOn (fun x ↦ L (f x)) s μ := fun x hx ↦
  let ⟨u, hu, hfu⟩ := hf x hx
  ⟨u, hu, L.integrable_comp hfu⟩

end MeasureTheory

/-! ### Commuting an extra derivative past iterated derivatives -/

section Calculus

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {n : ℕ} {x : E}

/-- `iteratedFDeriv_succ_apply_left` with the evaluation at a tuple moved inside the outermost
derivative: the `(n + 1)`-st derivative of `f` along `m` is the derivative along `m 0` of the
`n`-th derivative along `Fin.tail m`. -/
theorem iteratedFDeriv_succ_apply_left_of_differentiableAt
    (h : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) x) (m : Fin (n + 1) → E) :
    iteratedFDeriv ℝ (n + 1) f x m
      = fderiv ℝ (fun z ↦ iteratedFDeriv ℝ n f z (Fin.tail m)) x (m 0) := by
  rw [fderiv_continuousMultilinear_apply_const h, iteratedFDeriv_succ_apply_left]
  rfl

/-- For a smooth function, an extra derivative in the direction `v` may be taken either outside or
inside the `n` iterated derivatives. Iterating this is the symmetry of higher derivatives; only
this one-step form is needed here. -/
theorem ContDiff.fderiv_iteratedFDeriv_apply (hf : ContDiff ℝ ∞ f) (n : ℕ) (m : Fin n → E)
    (v x : E) :
    fderiv ℝ (fun z ↦ iteratedFDeriv ℝ n f z m) x v
      = iteratedFDeriv ℝ n (fun z ↦ fderiv ℝ f z v) x m := by
  induction n generalizing x with
  | zero => simp [iteratedFDeriv_zero_apply]
  | succ n ih =>
    have hd : ∀ g : E → F, ContDiff ℝ ∞ g → ∀ z, DifferentiableAt ℝ (iteratedFDeriv ℝ n g) z :=
      fun g hg z ↦
        (hg.iteratedFDeriv_right (m := 1) (i := n) (by simp)).differentiable one_ne_zero z
    have hG : ContDiff ℝ ∞ fun z ↦ iteratedFDeriv ℝ n f z (Fin.tail m) :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n ↦ E) F (Fin.tail m)).contDiff.comp
        (hf.iteratedFDeriv_right (m := ∞) (i := n) (by simp))
    have hψ : ContDiff ℝ ∞ fun z ↦ fderiv ℝ f z v :=
      (hf.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
    have hGd : Differentiable ℝ (fderiv ℝ fun z ↦ iteratedFDeriv ℝ n f z (Fin.tail m)) :=
      (hG.fderiv_right (m := ∞) le_rfl).differentiable (by simp)
    have hIH : (fun z ↦ iteratedFDeriv ℝ n (fun w ↦ fderiv ℝ f w v) z (Fin.tail m))
        = fun z ↦ fderiv ℝ (fun w ↦ iteratedFDeriv ℝ n f w (Fin.tail m)) z v :=
      funext fun z ↦ (ih _ z).symm
    have h1 : (fun z ↦ iteratedFDeriv ℝ (n + 1) f z m)
        = fun z ↦ fderiv ℝ (fun w ↦ iteratedFDeriv ℝ n f w (Fin.tail m)) z (m 0) :=
      funext fun z ↦ iteratedFDeriv_succ_apply_left_of_differentiableAt (hd f hf z) m
    rw [h1, iteratedFDeriv_succ_apply_left_of_differentiableAt (hd _ hψ x) m, hIH,
      fderiv_clm_apply (hGd x) (differentiableAt_const _),
      fderiv_clm_apply (hGd x) (differentiableAt_const _)]
    simp only [add_apply, ContinuousLinearMap.comp_apply, fderiv_fun_const, Pi.zero_apply,
      zero_apply, map_zero, zero_add, ContinuousLinearMap.flip_apply]
    exact (ContDiffAt.isSymmSndFDerivAt (x := x) hG.contDiffAt (by simp)).eq _ _

/-- For a smooth function, the `(n + 1)`-st derivative along `y` is the `n`-th derivative along
`Fin.tail y` of the derivative along `y 0`. Contrast `iteratedFDeriv_succ_apply_left`, which peels
off the *outermost* derivative, and `iteratedFDeriv_succ_apply_right`, which peels off the
innermost one but at the *last* index of the tuple. -/
theorem ContDiff.iteratedFDeriv_succ_apply_left' (hf : ContDiff ℝ ∞ f) (n : ℕ)
    (y : Fin (n + 1) → E) (x : E) :
    iteratedFDeriv ℝ (n + 1) f x y
      = iteratedFDeriv ℝ n (fun z ↦ fderiv ℝ f z (y 0)) x (Fin.tail y) := by
  rw [← hf.fderiv_iteratedFDeriv_apply n (Fin.tail y) (y 0) x,
    iteratedFDeriv_succ_apply_left_of_differentiableAt
      ((hf.iteratedFDeriv_right (m := 1) (i := n) (by simp)).differentiable one_ne_zero x) y]

/-- `ContDiff.iteratedFDeriv_succ_apply_left'` with the tuple written as a `Fin.cons`: for a smooth
function, differentiating `n + 1` times along `z :: y` is differentiating `n` times along `y` the
directional derivative in the direction `z`. This is the identity that splits a weak derivative
along a tuple of length `n + 1` into one of length `n` and one of length `1`; see
`HasWeakIteratedLineDerivOn.cons`. -/
theorem ContDiff.iteratedFDeriv_cons (hf : ContDiff ℝ ∞ f) (z : E) (y : Fin n → E) (x : E) :
    iteratedFDeriv ℝ (n + 1) f x (Fin.cons z y)
      = iteratedFDeriv ℝ n (fun t ↦ fderiv ℝ f t z) x y := by
  rw [hf.iteratedFDeriv_succ_apply_left' n (Fin.cons z y) x]
  simp

end Calculus

/-! ### Symmetry of the iterated derivative of a smooth function -/

section Symmetry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}

/-- Differentiating `f` successively along the entries of a list of directions, the head of the
list *innermost*: `listFDeriv [v₁, …, vₙ] f = ∂_{vₙ} ⋯ ∂_{v₁} f`.

Indexing by a list rather than by a tuple is what makes `listFDeriv_congr_perm` an induction on
`List.Perm`, whose `swap` constructor is exactly the transposition of the two innermost
derivatives; `ContDiff.listFDeriv_ofFn` identifies this with `iteratedFDeriv`. -/
noncomputable def listFDeriv (l : List E) (f : E → F) : E → F :=
  l.foldl (fun g v ↦ fun z ↦ fderiv ℝ g z v) f

/-- Differentiating along no directions at all leaves the function alone. -/
@[simp]
theorem listFDeriv_nil (f : E → F) : listFDeriv [] f = f := rfl

/-- Peeling the head of the list off `listFDeriv` takes the derivative along it first. -/
theorem listFDeriv_cons (v : E) (l : List E) (f : E → F) :
    listFDeriv (v :: l) f = listFDeriv l (fun z ↦ fderiv ℝ f z v) := rfl

/-- The derivative of a smooth function in a fixed direction is smooth. -/
theorem ContDiff.fderiv_apply_right (hf : ContDiff ℝ ∞ f) (v : E) :
    ContDiff ℝ ∞ fun z ↦ fderiv ℝ f z v :=
  (hf.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

/-- Differentiating a smooth function along the entries of `List.ofFn y` is its `n`-th derivative
evaluated at the tuple `y`. Each step is `ContDiff.iteratedFDeriv_succ_apply_left'`, which moves one
derivative from the outside of the iterated derivative to the inside. -/
theorem ContDiff.listFDeriv_ofFn (hf : ContDiff ℝ ∞ f) {n : ℕ} (y : Fin n → E) (x : E) :
    listFDeriv (List.ofFn y) f x = iteratedFDeriv ℝ n f x y := by
  induction n generalizing f with
  | zero => simp [iteratedFDeriv_zero_apply]
  | succ n ih =>
    rw [List.ofFn_succ, listFDeriv_cons, ih (hf.fderiv_apply_right (y 0)),
      hf.iteratedFDeriv_succ_apply_left' n y x]
    rfl

/-- **Two directional derivatives of a smooth function commute.** This is the symmetry of the
second derivative, in the form in which `listFDeriv_congr_perm` consumes it: an equality of
functions rather than of values, so that it may be applied under a further derivative. -/
theorem ContDiff.fderiv_fderiv_comm (hf : ContDiff ℝ ∞ f) (v w : E) :
    (fun z ↦ fderiv ℝ (fun y ↦ fderiv ℝ f y v) z w)
      = fun z ↦ fderiv ℝ (fun y ↦ fderiv ℝ f y w) z v := by
  funext x
  have h1 : (fun z ↦ iteratedFDeriv ℝ 1 f z ![v]) = fun z ↦ fderiv ℝ f z v := by
    funext z; rw [iteratedFDeriv_one_apply]; simp
  have h2 := hf.fderiv_iteratedFDeriv_apply 1 ![v] w x
  rw [h1, iteratedFDeriv_one_apply] at h2
  simpa using h2

/-- **Differentiating a smooth function along a list of directions does not depend on the order of
the list.** The induction is on `List.Perm`: its `swap` constructor is the transposition of the two
innermost derivatives, which is `ContDiff.fderiv_fderiv_comm`, and its `cons` constructor peels one
derivative off and applies the induction hypothesis to the differentiated function, which is smooth
again. -/
theorem listFDeriv_congr_perm {l₁ l₂ : List E} (h : l₁.Perm l₂) {f : E → F}
    (hf : ContDiff ℝ ∞ f) : listFDeriv l₁ f = listFDeriv l₂ f := by
  induction h generalizing f with
  | nil => rfl
  | cons a _ ih => rw [listFDeriv_cons, listFDeriv_cons, ih (hf.fderiv_apply_right a)]
  | swap a b l =>
    rw [listFDeriv_cons, listFDeriv_cons, listFDeriv_cons, listFDeriv_cons,
      hf.fderiv_fderiv_comm b a]
  | trans _ _ ih₁ ih₂ => rw [ih₁ hf, ih₂ hf]

/-- **The iterated derivative of a `C^∞` function is symmetric in its arguments**: it takes the same
value at two tuples of directions that are permutations of each other.

Mathlib has this for order two (`ContDiffAt.isSymmSndFDerivAt`) and, for any order, for analytic
functions (`ContDiffAt.domDomCongr_iteratedFDeriv`, which asks for `ω`-smoothness); this is the
`C^∞` statement of any order, obtained by transporting the commutation of two directional
derivatives along a `List.Perm`. The two tuples are allowed to have different lengths — the
hypothesis forces them to be equal — so that it applies to a pair of tuples whose lengths agree only
propositionally, such as `Fin n` and `Fin (∑ i, α i)`. -/
theorem ContDiff.iteratedFDeriv_congr_perm (hf : ContDiff ℝ ∞ f) {n₁ n₂ : ℕ}
    {y₁ : Fin n₁ → E} {y₂ : Fin n₂ → E} (h : (List.ofFn y₁).Perm (List.ofFn y₂)) (x : E) :
    iteratedFDeriv ℝ n₁ f x y₁ = iteratedFDeriv ℝ n₂ f x y₂ := by
  rw [← hf.listFDeriv_ofFn y₁ x, ← hf.listFDeriv_ofFn y₂ x, listFDeriv_congr_perm h hf]

end Symmetry

/-! ### Test functions -/

namespace TestFunction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E}

/-- A test function on `Ω` vanishes outside `Ω`. -/
theorem eq_zero_of_notMem (φ : 𝓓(Ω, F)) {x : E} (hx : x ∉ (Ω : Set E)) : φ x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h ↦ hx (φ.tsupport_subset h)

/-- The `n`-th derivative of a test function, evaluated at a fixed tuple of directions, is again
a test function. -/
noncomputable def iteratedFDerivApply (φ : 𝓓(Ω, F)) (n : ℕ) (y : Fin n → E) : 𝓓(Ω, F) where
  toFun x := iteratedFDeriv ℝ n φ x y
  contDiff' := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n ↦ E) F y).contDiff.comp
    (φ.contDiff.iteratedFDeriv_right (m := ∞) (i := n) (by simp))
  hasCompactSupport' := (φ.hasCompactSupport.iteratedFDeriv n).of_isClosed_subset
    isClosed_closure (tsupport_comp_subset (g := fun L : E [×n]→L[ℝ] F ↦ L y) rfl _)
  tsupport_subset' := (tsupport_comp_subset (g := fun L : E [×n]→L[ℝ] F ↦ L y) rfl _).trans
    ((tsupport_iteratedFDeriv_subset n).trans φ.tsupport_subset)

/-- `TestFunction.iteratedFDerivApply` as a function. -/
@[simp]
theorem iteratedFDerivApply_coe (φ : 𝓓(Ω, F)) (n : ℕ) (y : Fin n → E) :
    (φ.iteratedFDerivApply n y : E → F) = fun x ↦ iteratedFDeriv ℝ n φ x y :=
  rfl

/-- The value of `TestFunction.iteratedFDerivApply` at a point. -/
theorem iteratedFDerivApply_apply (φ : 𝓓(Ω, F)) (n : ℕ) (y : Fin n → E) (x : E) :
    φ.iteratedFDerivApply n y x = iteratedFDeriv ℝ n φ x y :=
  rfl

/-- A directional derivative of a test function is again a test function. -/
noncomputable def fderivApply (φ : 𝓓(Ω, F)) (v : E) : 𝓓(Ω, F) where
  toFun x := fderiv ℝ φ x v
  contDiff' := (φ.contDiff.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
  hasCompactSupport' := φ.hasCompactSupport.fderiv_apply ℝ v
  tsupport_subset' := (tsupport_fderiv_apply_subset ℝ v).trans φ.tsupport_subset

/-- `TestFunction.fderivApply` as a function. -/
@[simp]
theorem fderivApply_coe (φ : 𝓓(Ω, F)) (v : E) :
    (φ.fderivApply v : E → F) = fun x ↦ fderiv ℝ φ x v :=
  rfl

/-- The value of `TestFunction.fderivApply` at a point. -/
theorem fderivApply_apply (φ : 𝓓(Ω, F)) (v x : E) : φ.fderivApply v x = fderiv ℝ φ x v :=
  rfl

/-- The product of a test function with a smooth function is again a test function: it is smooth,
and its support is contained in that of the test function. -/
noncomputable def mulContDiff (φ : 𝓓(Ω, ℝ)) {g : E → ℝ} (hg : ContDiff ℝ ∞ g) : 𝓓(Ω, ℝ) where
  toFun x := φ x * g x
  contDiff' := φ.contDiff.mul hg
  hasCompactSupport' := φ.hasCompactSupport.mul_right
  tsupport_subset' := tsupport_mul_subset_left.trans φ.tsupport_subset

/-- `TestFunction.mulContDiff` as a function. -/
@[simp]
theorem mulContDiff_coe (φ : 𝓓(Ω, ℝ)) {g : E → ℝ} (hg : ContDiff ℝ ∞ g) :
    (φ.mulContDiff hg : E → ℝ) = fun x ↦ φ x * g x :=
  rfl

end TestFunction

/-! ### The weak derivative -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E} {μ : Measure E} {n : ℕ} {f : E → F} {w : E → E [×n]→L[ℝ] F}

/-- `HasWeakIteratedFDerivOn n f w Ω μ` says that `w` is an `n`-th *weak derivative* of `f` on the
open set `Ω`: both are locally integrable there, and the classical integration by parts formula

`∫_Ω (∂^n φ x) y • f x dx = (-1)^n ∫_Ω φ x • (w x) y dx`

holds for every test function `φ ∈ C_0^∞(Ω)` and every tuple `y` of `n` directions. A tuple of
directions plays the role of a multi-index of length `n`, so this is the definition of Atkinson and
Han, *Theoretical Numerical Analysis: A Functional Analysis Framework*, 3rd edition,
Definition 7.1.3, taken for all multi-indices of length `n` at once. -/
structure HasWeakIteratedFDerivOn (n : ℕ) (f : E → F) (w : E → E [×n]→L[ℝ] F) (Ω : Opens E)
    (μ : Measure E) : Prop where
  /-- A function with a weak derivative is locally integrable. -/
  locallyIntegrableOn : LocallyIntegrableOn f Ω μ
  /-- A weak derivative is locally integrable. -/
  locallyIntegrableOn_weakDeriv : LocallyIntegrableOn w Ω μ
  /-- The integration by parts formula defining the weak derivative. -/
  integral_smul_eq (φ : 𝓓(Ω, ℝ)) (y : Fin n → E) :
    ∫ x in (Ω : Set E), iteratedFDeriv ℝ n φ x y • f x ∂μ
      = (-1 : ℝ) ^ n • ∫ x in (Ω : Set E), φ x • w x y ∂μ

/-- `HasWeakFDerivOn f w Ω μ` says that `w : E → E →L[ℝ] F` is a first-order weak derivative of
`f` on the open set `Ω`. -/
def HasWeakFDerivOn (f : E → F) (w : E → E →L[ℝ] F) (Ω : Opens E) (μ : Measure E) : Prop :=
  HasWeakIteratedFDerivOn 1 f (fun x ↦ (continuousMultilinearCurryFin1 ℝ E F).symm (w x)) Ω μ

namespace HasWeakIteratedFDerivOn

section Integrals

variable [OpensMeasurableSpace E]

/-- The product of a test function on `Ω` with a function having a weak derivative there is
integrable. -/
theorem integrable_smul (h : HasWeakIteratedFDerivOn n f w Ω μ) (φ : 𝓓(Ω, ℝ)) :
    Integrable (fun x ↦ φ x • f x) μ :=
  LocallyIntegrableOn.integrable_smul_left_of_tsupport_subset h.locallyIntegrableOn
    φ.contDiff.continuous φ.hasCompactSupport φ.tsupport_subset

/-- The product of a test function on `Ω` with a weak derivative is integrable. -/
theorem integrable_smul_weakDeriv (h : HasWeakIteratedFDerivOn n f w Ω μ) (φ : 𝓓(Ω, ℝ)) :
    Integrable (fun x ↦ φ x • w x) μ :=
  LocallyIntegrableOn.integrable_smul_left_of_tsupport_subset h.locallyIntegrableOn_weakDeriv
    φ.contDiff.continuous φ.hasCompactSupport φ.tsupport_subset

/-- The product of a test function on `Ω` with a weak derivative evaluated at a fixed tuple of
directions is integrable. -/
theorem integrable_smul_weakDeriv_apply (h : HasWeakIteratedFDerivOn n f w Ω μ) (φ : 𝓓(Ω, ℝ))
    (y : Fin n → E) : Integrable (fun x ↦ φ x • w x y) μ :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n ↦ E) F y).integrable_comp
    (h.integrable_smul_weakDeriv φ)

omit [OpensMeasurableSpace E] in
omit [OpensMeasurableSpace E] in
/-- The integration by parts formula defining the weak derivative, with the integrals taken over
the whole space: the test function vanishes outside `Ω`, so nothing changes. -/
theorem integral_smul_eq' (h : HasWeakIteratedFDerivOn n f w Ω μ) (φ : 𝓓(Ω, ℝ))
    (y : Fin n → E) :
    ∫ x, iteratedFDeriv ℝ n φ x y • f x ∂μ = (-1 : ℝ) ^ n • ∫ x, φ x • w x y ∂μ := by
  have e1 : ∫ x in (Ω : Set E), iteratedFDeriv ℝ n φ x y • f x ∂μ
      = ∫ x, iteratedFDeriv ℝ n φ x y • f x ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [show iteratedFDeriv ℝ n (φ : E → ℝ) x y = 0 from
        (φ.iteratedFDerivApply n y).eq_zero_of_notMem hx, zero_smul]
  have e2 : ∫ x in (Ω : Set E), φ x • w x y ∂μ = ∫ x, φ x • w x y ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [φ.eq_zero_of_notMem hx, zero_smul]
  rw [← e1, ← e2]
  exact h.integral_smul_eq φ y

omit [OpensMeasurableSpace E] in
/-- The weak derivative relation only sees the functions up to a null set of `Ω`: changing either
`f` or `w` on a `μ.restrict Ω`-null set preserves it. -/
theorem congr_ae {f' : E → F} {w' : E → E [×n]→L[ℝ] F} (h : HasWeakIteratedFDerivOn n f w Ω μ)
    (hf : f =ᵐ[μ.restrict (Ω : Set E)] f') (hw : w =ᵐ[μ.restrict (Ω : Set E)] w') :
    HasWeakIteratedFDerivOn n f' w' Ω μ where
  locallyIntegrableOn := h.locallyIntegrableOn.congr hf
  locallyIntegrableOn_weakDeriv := h.locallyIntegrableOn_weakDeriv.congr hw
  integral_smul_eq φ y := by
    have e1 : ∫ x in (Ω : Set E), iteratedFDeriv ℝ n φ x y • f' x ∂μ
        = ∫ x in (Ω : Set E), iteratedFDeriv ℝ n φ x y • f x ∂μ :=
      integral_congr_ae (by filter_upwards [hf] with x hx; rw [hx])
    have e2 : ∫ x in (Ω : Set E), φ x • w' x y ∂μ = ∫ x in (Ω : Set E), φ x • w x y ∂μ :=
      integral_congr_ae (by filter_upwards [hw] with x hx; rw [hx])
    rw [e1, e2]
    exact h.integral_smul_eq φ y

omit [OpensMeasurableSpace E] in
/-- A weak derivative on `Ω` is a weak derivative on every smaller open set. -/
theorem mono {Ω' : Opens E} (h : HasWeakIteratedFDerivOn n f w Ω μ) (hΩ : Ω' ≤ Ω) :
    HasWeakIteratedFDerivOn n f w Ω' μ where
  locallyIntegrableOn := h.locallyIntegrableOn.mono_set hΩ
  locallyIntegrableOn_weakDeriv := h.locallyIntegrableOn_weakDeriv.mono_set hΩ
  integral_smul_eq φ y := by
    have e1 : ∫ x in (Ω' : Set E), iteratedFDeriv ℝ n φ x y • f x ∂μ
        = ∫ x, iteratedFDeriv ℝ n φ x y • f x ∂μ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
        rw [show iteratedFDeriv ℝ n (φ : E → ℝ) x y = 0 from
          (φ.iteratedFDerivApply n y).eq_zero_of_notMem hx, zero_smul]
    have e2 : ∫ x in (Ω' : Set E), φ x • w x y ∂μ = ∫ x, φ x • w x y ∂μ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
        rw [φ.eq_zero_of_notMem hx, zero_smul]
    rw [e1, e2]
    exact h.integral_smul_eq' ⟨φ, φ.contDiff, φ.hasCompactSupport,
      φ.tsupport_subset.trans hΩ⟩ y

end Integrals

variable [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F]

/-- **A weak derivative is unique up to a null set**: Atkinson and Han, *Theoretical Numerical
Analysis: A Functional Analysis Framework*, 3rd edition, Lemma 7.1.4. This is Mathlib's
generalized variational lemma `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` (Atkinson–Han,
Lemma 7.1.2) applied to the difference of the two weak derivatives. -/
theorem ae_eq {w₁ w₂ : E → E [×n]→L[ℝ] F} (h₁ : HasWeakIteratedFDerivOn n f w₁ Ω μ)
    (h₂ : HasWeakIteratedFDerivOn n f w₂ Ω μ) : ∀ᵐ x ∂μ, x ∈ (Ω : Set E) → w₁ x = w₂ x := by
  have key : ∀ᵐ x ∂μ, x ∈ (Ω : Set E) → w₁ x - w₂ x = 0 := by
    refine Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (LocallyIntegrableOn.sub h₁.locallyIntegrableOn_weakDeriv
        h₂.locallyIntegrableOn_weakDeriv) fun g hg h'g hgs ↦ ?_
    set φ : 𝓓(Ω, ℝ) := ⟨g, hg, h'g, hgs⟩ with hφ
    have e1 : Integrable (fun x ↦ g x • w₁ x) μ := h₁.integrable_smul_weakDeriv φ
    have e2 : Integrable (fun x ↦ g x • w₂ x) μ := h₂.integrable_smul_weakDeriv φ
    have key : ∫ x, g x • w₁ x ∂μ = ∫ x, g x • w₂ x ∂μ := by
      refine ContinuousMultilinearMap.ext fun y ↦ ?_
      rw [ContinuousMultilinearMap.integral_apply e1, ContinuousMultilinearMap.integral_apply e2]
      refine smul_right_injective F (pow_ne_zero n (by norm_num : (-1 : ℝ) ≠ 0)) ?_
      exact (h₁.integral_smul_eq' φ y).symm.trans (h₂.integral_smul_eq' φ y)
    have hsub : (fun x ↦ g x • (w₁ x - w₂ x)) = fun x ↦ g x • w₁ x - g x • w₂ x :=
      funext fun x ↦ smul_sub _ _ _
    rw [hsub, integral_sub e1 e2, key, sub_self]
  filter_upwards [key] with x hx hxΩ using sub_eq_zero.mp (hx hxΩ)

end HasWeakIteratedFDerivOn

/-! ### Linearity -/

namespace HasWeakIteratedFDerivOn

variable [OpensMeasurableSpace E]

omit [OpensMeasurableSpace E] in
/-- The zero function has zero weak derivative of every order. -/
protected theorem zero : HasWeakIteratedFDerivOn n (0 : E → F) 0 Ω μ where
  locallyIntegrableOn := locallyIntegrable_zero.locallyIntegrableOn _
  locallyIntegrableOn_weakDeriv := locallyIntegrable_zero.locallyIntegrableOn _
  integral_smul_eq φ y := by simp

/-- Weak differentiation is additive; half of Atkinson and Han, *Theoretical Numerical Analysis:
A Functional Analysis Framework*, 3rd edition, Proposition 7.1.10. -/
protected theorem add {f₁ f₂ : E → F} {w₁ w₂ : E → E [×n]→L[ℝ] F}
    (h₁ : HasWeakIteratedFDerivOn n f₁ w₁ Ω μ) (h₂ : HasWeakIteratedFDerivOn n f₂ w₂ Ω μ) :
    HasWeakIteratedFDerivOn n (f₁ + f₂) (w₁ + w₂) Ω μ where
  locallyIntegrableOn := LocallyIntegrableOn.add h₁.locallyIntegrableOn h₂.locallyIntegrableOn
  locallyIntegrableOn_weakDeriv :=
    LocallyIntegrableOn.add h₁.locallyIntegrableOn_weakDeriv h₂.locallyIntegrableOn_weakDeriv
  integral_smul_eq φ y := by
    have i₁ := (h₁.integrable_smul (φ.iteratedFDerivApply n y)).integrableOn (s := (Ω : Set E))
    have i₂ := (h₂.integrable_smul (φ.iteratedFDerivApply n y)).integrableOn (s := (Ω : Set E))
    simp only [TestFunction.iteratedFDerivApply_apply] at i₁ i₂
    have j₁ := (h₁.integrable_smul_weakDeriv_apply φ y).integrableOn (s := (Ω : Set E))
    have j₂ := (h₂.integrable_smul_weakDeriv_apply φ y).integrableOn (s := (Ω : Set E))
    simp only [Pi.add_apply, add_apply, smul_add]
    rw [integral_add i₁ i₂, integral_add j₁ j₂, h₁.integral_smul_eq, h₂.integral_smul_eq, smul_add]

omit [OpensMeasurableSpace E] in
/-- Weak differentiation commutes with scalar multiplication; half of Atkinson and Han,
*Theoretical Numerical Analysis: A Functional Analysis Framework*, 3rd edition,
Proposition 7.1.10. -/
protected theorem const_smul (h : HasWeakIteratedFDerivOn n f w Ω μ) (c : ℝ) :
    HasWeakIteratedFDerivOn n (c • f) (c • w) Ω μ where
  locallyIntegrableOn := h.locallyIntegrableOn.smul c
  locallyIntegrableOn_weakDeriv := h.locallyIntegrableOn_weakDeriv.smul c
  integral_smul_eq φ y := by
    simp only [Pi.smul_apply, smul_apply, smul_comm _ c, integral_smul, h.integral_smul_eq]

omit [OpensMeasurableSpace E] in
/-- Weak differentiation commutes with negation. -/
protected theorem neg (h : HasWeakIteratedFDerivOn n f w Ω μ) :
    HasWeakIteratedFDerivOn n (-f) (-w) Ω μ where
  locallyIntegrableOn := h.locallyIntegrableOn.neg
  locallyIntegrableOn_weakDeriv := h.locallyIntegrableOn_weakDeriv.neg
  integral_smul_eq φ y := by
    simp only [Pi.neg_apply, neg_apply, smul_neg, integral_neg, h.integral_smul_eq, smul_neg]

/-- Weak differentiation commutes with subtraction. -/
protected theorem sub {f₁ f₂ : E → F} {w₁ w₂ : E → E [×n]→L[ℝ] F}
    (h₁ : HasWeakIteratedFDerivOn n f₁ w₁ Ω μ) (h₂ : HasWeakIteratedFDerivOn n f₂ w₂ Ω μ) :
    HasWeakIteratedFDerivOn n (f₁ - f₂) (w₁ - w₂) Ω μ := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg

/-- **Weak differentiation is linear**: Atkinson and Han, *Theoretical Numerical Analysis:
A Functional Analysis Framework*, 3rd edition, Proposition 7.1.10. -/
theorem const_smul_add_const_smul {f₁ f₂ : E → F} {w₁ w₂ : E → E [×n]→L[ℝ] F}
    (h₁ : HasWeakIteratedFDerivOn n f₁ w₁ Ω μ) (h₂ : HasWeakIteratedFDerivOn n f₂ w₂ Ω μ)
    (c₁ c₂ : ℝ) :
    HasWeakIteratedFDerivOn n (c₁ • f₁ + c₂ • f₂) (c₁ • w₁ + c₂ • w₂) Ω μ :=
  (h₁.const_smul c₁).add (h₂.const_smul c₂)

end HasWeakIteratedFDerivOn

/-! ### Weak derivatives along a fixed tuple of directions -/

section Line

variable {y : Fin n → E} {w : E → F}

/-- `HasWeakIteratedLineDerivOn y f w Ω μ` says that `w : E → F` is a *weak derivative of `f` along
the tuple `y` of directions* on the open set `Ω`: both are locally integrable there, and the
integration by parts formula

`∫_Ω (∂^n φ x) y • f x dx = (-1)^n ∫_Ω φ x • w x dx`

holds for every test function `φ ∈ C_0^∞(Ω)`, where `n` is the length of `y`. Where
`HasWeakIteratedFDerivOn` takes all the tuples of a given length at once, and so is valued in the
continuous `n`-linear maps, this takes one tuple at a time: it is the definition of Atkinson and
Han, *Theoretical Numerical Analysis: A Functional Analysis Framework*, 3rd edition,
Definition 7.1.3, for the single multi-index that the tuple names. -/
structure HasWeakIteratedLineDerivOn {n : ℕ} (y : Fin n → E) (f : E → F) (w : E → F)
    (Ω : Opens E) (μ : Measure E) : Prop where
  /-- A function with a weak derivative along a tuple of directions is locally integrable. -/
  locallyIntegrableOn : LocallyIntegrableOn f Ω μ
  /-- A weak derivative along a tuple of directions is locally integrable. -/
  locallyIntegrableOn_weakDeriv : LocallyIntegrableOn w Ω μ
  /-- The integration by parts formula defining the weak derivative along a tuple of directions. -/
  integral_smul_eq (φ : 𝓓(Ω, ℝ)) :
    ∫ x in (Ω : Set E), iteratedFDeriv ℝ n φ x y • f x ∂μ
      = (-1 : ℝ) ^ n • ∫ x in (Ω : Set E), φ x • w x ∂μ

/-- Evaluating a weak derivative of order `n` at a fixed tuple `y` of directions gives a weak
derivative along `y`; so `HasWeakIteratedFDerivOn` asserts the tuple-by-tuple notion for every
tuple of that length at once. -/
theorem HasWeakIteratedFDerivOn.lineDeriv {w : E → E [×n]→L[ℝ] F}
    (h : HasWeakIteratedFDerivOn n f w Ω μ) (y : Fin n → E) :
    HasWeakIteratedLineDerivOn y f (fun x ↦ w x y) Ω μ where
  locallyIntegrableOn := h.locallyIntegrableOn
  locallyIntegrableOn_weakDeriv := h.locallyIntegrableOn_weakDeriv.comp_continuousLinearMap
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n ↦ E) F y)
  integral_smul_eq φ := h.integral_smul_eq φ y

namespace HasWeakIteratedLineDerivOn

variable [OpensMeasurableSpace E]

omit [OpensMeasurableSpace E] in
/-- Along a tuple of length `0` the function is its own weak derivative. The hypothesis is written
`n = 0` rather than fixing the tuple to be empty, so that it applies to a tuple whose length is
only propositionally zero. -/
theorem of_length_eq_zero (hn : n = 0) (y : Fin n → E) (hf : LocallyIntegrableOn f Ω μ) :
    HasWeakIteratedLineDerivOn y f f Ω μ := by
  subst hn
  exact ⟨hf, hf, fun φ ↦ by simp⟩

omit [OpensMeasurableSpace E] in
/-- The integration by parts formula defining the weak derivative along a tuple of directions, with
the integrals taken over the whole space: the test function vanishes outside `Ω`, so nothing
changes. -/
theorem integral_smul_eq' (h : HasWeakIteratedLineDerivOn y f w Ω μ) (φ : 𝓓(Ω, ℝ)) :
    ∫ x, iteratedFDeriv ℝ n φ x y • f x ∂μ = (-1 : ℝ) ^ n • ∫ x, φ x • w x ∂μ := by
  have e1 : ∫ x in (Ω : Set E), iteratedFDeriv ℝ n φ x y • f x ∂μ
      = ∫ x, iteratedFDeriv ℝ n φ x y • f x ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [show iteratedFDeriv ℝ n (φ : E → ℝ) x y = 0 from
        (φ.iteratedFDerivApply n y).eq_zero_of_notMem hx, zero_smul]
  have e2 : ∫ x in (Ω : Set E), φ x • w x ∂μ = ∫ x, φ x • w x ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [φ.eq_zero_of_notMem hx, zero_smul]
  rw [← e1, ← e2]
  exact h.integral_smul_eq φ

omit [OpensMeasurableSpace E] in
/-- The weak derivative along a tuple only sees the functions up to a null set of `Ω`. -/
theorem congr_ae {f' w' : E → F} (h : HasWeakIteratedLineDerivOn y f w Ω μ)
    (hf : f =ᵐ[μ.restrict (Ω : Set E)] f') (hw : w =ᵐ[μ.restrict (Ω : Set E)] w') :
    HasWeakIteratedLineDerivOn y f' w' Ω μ where
  locallyIntegrableOn := h.locallyIntegrableOn.congr hf
  locallyIntegrableOn_weakDeriv := h.locallyIntegrableOn_weakDeriv.congr hw
  integral_smul_eq φ := by
    have e1 : ∫ x in (Ω : Set E), iteratedFDeriv ℝ n φ x y • f' x ∂μ
        = ∫ x in (Ω : Set E), iteratedFDeriv ℝ n φ x y • f x ∂μ :=
      integral_congr_ae (by filter_upwards [hf] with x hx; rw [hx])
    have e2 : ∫ x in (Ω : Set E), φ x • w' x ∂μ = ∫ x in (Ω : Set E), φ x • w x ∂μ :=
      integral_congr_ae (by filter_upwards [hw] with x hx; rw [hx])
    rw [e1, e2]
    exact h.integral_smul_eq φ

omit [OpensMeasurableSpace E] in
/-- A weak derivative along a tuple of directions on `Ω` is a weak derivative along the same tuple
on every smaller open set. -/
theorem mono {Ω' : Opens E} (h : HasWeakIteratedLineDerivOn y f w Ω μ) (hΩ : Ω' ≤ Ω) :
    HasWeakIteratedLineDerivOn y f w Ω' μ where
  locallyIntegrableOn := h.locallyIntegrableOn.mono_set hΩ
  locallyIntegrableOn_weakDeriv := h.locallyIntegrableOn_weakDeriv.mono_set hΩ
  integral_smul_eq φ := by
    have e1 : ∫ x in (Ω' : Set E), iteratedFDeriv ℝ n φ x y • f x ∂μ
        = ∫ x, iteratedFDeriv ℝ n φ x y • f x ∂μ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
        rw [show iteratedFDeriv ℝ n (φ : E → ℝ) x y = 0 from
          (φ.iteratedFDerivApply n y).eq_zero_of_notMem hx, zero_smul]
    have e2 : ∫ x in (Ω' : Set E), φ x • w x ∂μ = ∫ x, φ x • w x ∂μ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
        rw [φ.eq_zero_of_notMem hx, zero_smul]
    rw [e1, e2]
    exact h.integral_smul_eq' ⟨φ, φ.contDiff, φ.hasCompactSupport,
      φ.tsupport_subset.trans hΩ⟩

omit [OpensMeasurableSpace E] in
/-- The zero function has zero weak derivative along every tuple of directions. -/
protected theorem zero : HasWeakIteratedLineDerivOn y (0 : E → F) 0 Ω μ where
  locallyIntegrableOn := locallyIntegrable_zero.locallyIntegrableOn _
  locallyIntegrableOn_weakDeriv := locallyIntegrable_zero.locallyIntegrableOn _
  integral_smul_eq φ := by simp

/-- The product of a test function on `Ω` with a function having a weak derivative along a tuple is
integrable. -/
theorem integrable_smul (h : HasWeakIteratedLineDerivOn y f w Ω μ) (φ : 𝓓(Ω, ℝ)) :
    Integrable (fun x ↦ φ x • f x) μ :=
  LocallyIntegrableOn.integrable_smul_left_of_tsupport_subset h.locallyIntegrableOn
    φ.contDiff.continuous φ.hasCompactSupport φ.tsupport_subset

/-- The product of a test function on `Ω` with a weak derivative along a tuple is integrable. -/
theorem integrable_smul_weakDeriv (h : HasWeakIteratedLineDerivOn y f w Ω μ) (φ : 𝓓(Ω, ℝ)) :
    Integrable (fun x ↦ φ x • w x) μ :=
  LocallyIntegrableOn.integrable_smul_left_of_tsupport_subset h.locallyIntegrableOn_weakDeriv
    φ.contDiff.continuous φ.hasCompactSupport φ.tsupport_subset

/-- Weak differentiation along a tuple of directions is additive. -/
protected theorem add {f₁ f₂ w₁ w₂ : E → F} (h₁ : HasWeakIteratedLineDerivOn y f₁ w₁ Ω μ)
    (h₂ : HasWeakIteratedLineDerivOn y f₂ w₂ Ω μ) :
    HasWeakIteratedLineDerivOn y (f₁ + f₂) (w₁ + w₂) Ω μ where
  locallyIntegrableOn := LocallyIntegrableOn.add h₁.locallyIntegrableOn h₂.locallyIntegrableOn
  locallyIntegrableOn_weakDeriv :=
    LocallyIntegrableOn.add h₁.locallyIntegrableOn_weakDeriv h₂.locallyIntegrableOn_weakDeriv
  integral_smul_eq φ := by
    have i₁ := (h₁.integrable_smul (φ.iteratedFDerivApply n y)).integrableOn (s := (Ω : Set E))
    have i₂ := (h₂.integrable_smul (φ.iteratedFDerivApply n y)).integrableOn (s := (Ω : Set E))
    simp only [TestFunction.iteratedFDerivApply_apply] at i₁ i₂
    have j₁ := (h₁.integrable_smul_weakDeriv φ).integrableOn (s := (Ω : Set E))
    have j₂ := (h₂.integrable_smul_weakDeriv φ).integrableOn (s := (Ω : Set E))
    simp only [Pi.add_apply, smul_add]
    rw [integral_add i₁ i₂, integral_add j₁ j₂, h₁.integral_smul_eq, h₂.integral_smul_eq, smul_add]

omit [OpensMeasurableSpace E] in
/-- Weak differentiation along a tuple of directions commutes with scalar multiplication. -/
protected theorem const_smul (h : HasWeakIteratedLineDerivOn y f w Ω μ) (c : ℝ) :
    HasWeakIteratedLineDerivOn y (c • f) (c • w) Ω μ where
  locallyIntegrableOn := h.locallyIntegrableOn.smul c
  locallyIntegrableOn_weakDeriv := h.locallyIntegrableOn_weakDeriv.smul c
  integral_smul_eq φ := by
    simp only [Pi.smul_apply, smul_comm _ c, integral_smul, h.integral_smul_eq]

omit [OpensMeasurableSpace E] in
/-- Weak differentiation along a tuple of directions commutes with negation. -/
protected theorem neg (h : HasWeakIteratedLineDerivOn y f w Ω μ) :
    HasWeakIteratedLineDerivOn y (-f) (-w) Ω μ where
  locallyIntegrableOn := h.locallyIntegrableOn.neg
  locallyIntegrableOn_weakDeriv := h.locallyIntegrableOn_weakDeriv.neg
  integral_smul_eq φ := by
    simp only [Pi.neg_apply, smul_neg, integral_neg, h.integral_smul_eq, smul_neg]

/-- Weak differentiation along a tuple of directions commutes with subtraction. -/
protected theorem sub {f₁ f₂ w₁ w₂ : E → F} (h₁ : HasWeakIteratedLineDerivOn y f₁ w₁ Ω μ)
    (h₂ : HasWeakIteratedLineDerivOn y f₂ w₂ Ω μ) :
    HasWeakIteratedLineDerivOn y (f₁ - f₂) (w₁ - w₂) Ω μ := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg

omit [MeasurableSpace E] [OpensMeasurableSpace E] in
/-- The defining identity of the weak derivative along a tuple `z :: y`, read through
`ContDiff.iteratedFDeriv_cons`: testing against `∂^{n+1} φ` along `z :: y` is testing against
`∂^n (∂_z φ)` along `y`, and `∂_z φ` is again a test function. -/
theorem _root_.TestFunction.iteratedFDeriv_cons (φ : 𝓓(Ω, ℝ)) (z : E) (y : Fin n → E) (x : E) :
    iteratedFDeriv ℝ (n + 1) (φ : E → ℝ) x (Fin.cons z y)
      = iteratedFDeriv ℝ n (φ.fderivApply z : E → ℝ) x y :=
  φ.contDiff.iteratedFDeriv_cons z y x

omit [OpensMeasurableSpace E] in
/-- **The composition rule for weak derivatives along tuples of directions**: if `w` is a weak
derivative of `f` along the tuple `y` of length `n`, and `u` is a weak derivative of `w` along the
single direction `z`, then `u` is a weak derivative of `f` along the tuple `z :: y` of length
`n + 1`.

Together with its converse `HasWeakIteratedLineDerivOn.of_cons` this is the bridge between a weak
derivative of order `n` and `n` iterated weak derivatives of order one, which is what lets an
induction on the order build weak derivatives one direction at a time — as in the Leibniz rule for
a product with a smooth factor. The proof is the defining identity applied twice, to the test
function `∂_z φ` and to `φ`; the signs `(-1)^n` and `(-1)^1` multiply to the `(-1)^{n+1}` that the
definition asks for at length `n + 1`. -/
theorem cons {z : E} {u : E → F} (h : HasWeakIteratedLineDerivOn y f w Ω μ)
    (h' : HasWeakIteratedLineDerivOn ![z] w u Ω μ) :
    HasWeakIteratedLineDerivOn (Fin.cons z y) f u Ω μ where
  locallyIntegrableOn := h.locallyIntegrableOn
  locallyIntegrableOn_weakDeriv := h'.locallyIntegrableOn_weakDeriv
  integral_smul_eq φ := by
    have e1 : ∫ x in (Ω : Set E), iteratedFDeriv ℝ (n + 1) (φ : E → ℝ) x (Fin.cons z y) • f x ∂μ
        = ∫ x in (Ω : Set E), iteratedFDeriv ℝ n (φ.fderivApply z : E → ℝ) x y • f x ∂μ := by
      simp_rw [TestFunction.iteratedFDeriv_cons φ z y]
    have e2 : ∫ x in (Ω : Set E), (φ.fderivApply z) x • w x ∂μ
        = ∫ x in (Ω : Set E), iteratedFDeriv ℝ 1 (φ : E → ℝ) x ![z] • w x ∂μ := by
      simp [iteratedFDeriv_one_apply]
    rw [e1, h.integral_smul_eq, e2, h'.integral_smul_eq, smul_smul]
    congr 1
    ring

omit [OpensMeasurableSpace E] in
/-- **The converse of the composition rule**: if `w` is a weak derivative of `f` along the tuple
`y` and `u` is a weak derivative of `f` along the longer tuple `z :: y`, then `u` is a weak
derivative of `w` along the single direction `z`.

This is what makes the weak derivatives of a Sobolev function a *chain*: the derivative of order
`n + 1` along `z :: y` is the first-order derivative, in the direction `z`, of the derivative of
order `n` along `y`. -/
theorem of_cons {z : E} {u : E → F} (h : HasWeakIteratedLineDerivOn y f w Ω μ)
    (h' : HasWeakIteratedLineDerivOn (Fin.cons z y) f u Ω μ) :
    HasWeakIteratedLineDerivOn ![z] w u Ω μ where
  locallyIntegrableOn := h.locallyIntegrableOn_weakDeriv
  locallyIntegrableOn_weakDeriv := h'.locallyIntegrableOn_weakDeriv
  integral_smul_eq φ := by
    have k1 := h.integral_smul_eq (φ.fderivApply z)
    have k2 := h'.integral_smul_eq φ
    simp_rw [TestFunction.iteratedFDeriv_cons φ z y] at k2
    have e2 : ∫ x in (Ω : Set E), (φ.fderivApply z) x • w x ∂μ
        = ∫ x in (Ω : Set E), iteratedFDeriv ℝ 1 (φ : E → ℝ) x ![z] • w x ∂μ := by
      simp [iteratedFDeriv_one_apply]
    have key : ((-1 : ℝ) ^ n) •
          ∫ x in (Ω : Set E), iteratedFDeriv ℝ 1 (φ : E → ℝ) x ![z] • w x ∂μ
        = ((-1 : ℝ) ^ n) • ((-1 : ℝ) ^ 1 • ∫ x in (Ω : Set E), φ x • u x ∂μ) := by
      rw [← e2, ← k1, k2, smul_smul]
      congr 1
      ring
    exact smul_right_injective F (pow_ne_zero n (by norm_num : (-1 : ℝ) ≠ 0)) key

/-- **The Leibniz rule for a smooth factor**: if `w` is a weak derivative of `f` along a tuple of
one direction on `Ω` and `g` is smooth, then `f g` has the weak derivative `w g + f ∂g` along the
same direction, `∂g` being the classical derivative of `g` in that direction. Only one factor is
smooth here; Atkinson and Han, *Theoretical Numerical Analysis: A Functional Analysis Framework*,
3rd edition, Proposition 7.1.11 allows both factors to be merely locally integrable with locally
integrable weak derivatives, which needs mollification in `L^p` and is not proved here. -/
theorem mul_contDiff {m : ℕ} {f' w' : E → ℝ} {y' : Fin m → E} {Ω : Opens E} {μ : Measure E}
    (h : HasWeakIteratedLineDerivOn y' f' w' Ω μ) (hm : m = 1) {g : E → ℝ}
    (hg : ContDiff ℝ ∞ g) :
    HasWeakIteratedLineDerivOn y' (fun x ↦ f' x * g x)
      (fun x ↦ w' x * g x + f' x * iteratedFDeriv ℝ m g x y') Ω μ := by
  subst hm
  simp only [iteratedFDeriv_one_apply]
  have hgd : ContDiff ℝ ∞ fun x ↦ fderiv ℝ g x (y' 0) :=
    (hg.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
  refine ⟨h.locallyIntegrableOn.mul_continuous hg.continuous,
    (h.locallyIntegrableOn_weakDeriv.mul_continuous hg.continuous).add
      (h.locallyIntegrableOn.mul_continuous hgd.continuous), fun φ ↦ ?_⟩
  set ψ : 𝓓(Ω, ℝ) := φ.mulContDiff hg with hψ
  set χ : 𝓓(Ω, ℝ) := φ.mulContDiff hgd with hχ
  set θ : 𝓓(Ω, ℝ) := (φ.fderivApply (y' 0)).mulContDiff hg with hθ
  have hexp : ∀ x, iteratedFDeriv ℝ 1 (ψ : E → ℝ) x y' = χ x + θ x := by
    intro x
    rw [iteratedFDeriv_one_apply]
    change fderiv ℝ (fun z ↦ φ z * g z) x (y' 0) = φ x * fderiv ℝ g x (y' 0)
      + fderiv ℝ (φ : E → ℝ) x (y' 0) * g x
    rw [fderiv_fun_mul (φ.contDiff.differentiable (by simp) x) (hg.differentiable (by simp) x)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have Iχ := (h.integrable_smul χ).integrableOn (s := (Ω : Set E))
  have Iθ := (h.integrable_smul θ).integrableOn (s := (Ω : Set E))
  have Iψ := (h.integrable_smul_weakDeriv ψ).integrableOn (s := (Ω : Set E))
  have e1 : ∫ x in (Ω : Set E), iteratedFDeriv ℝ 1 (ψ : E → ℝ) x y' • f' x ∂μ
      = (∫ x in (Ω : Set E), χ x • f' x ∂μ) + ∫ x in (Ω : Set E), θ x • f' x ∂μ := by
    rw [← integral_add Iχ Iθ]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by
      simp only [hexp x, add_smul])
  have e2 : ∫ x in (Ω : Set E), φ x • (w' x * g x + f' x * fderiv ℝ g x (y' 0)) ∂μ
      = (∫ x in (Ω : Set E), ψ x • w' x ∂μ) + ∫ x in (Ω : Set E), χ x • f' x ∂μ := by
    rw [← integral_add Iψ Iχ]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by
      simp only [hψ, hχ, TestFunction.mulContDiff_coe, smul_eq_mul]; ring)
  have e3 : ∫ x in (Ω : Set E), iteratedFDeriv ℝ 1 (φ : E → ℝ) x y' • (f' x * g x) ∂μ
      = ∫ x in (Ω : Set E), θ x • f' x ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by
      simp only [hθ, TestFunction.mulContDiff_coe, TestFunction.fderivApply_coe,
        iteratedFDeriv_one_apply, smul_eq_mul]
      ring)
  have key := h.integral_smul_eq ψ
  rw [e1] at key
  rw [e3, e2]
  simp only [pow_one, neg_one_smul] at key ⊢
  linarith [key]

variable [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F]

/-- **A weak derivative along a tuple of directions is unique up to a null set**: the
tuple-by-tuple form of Atkinson and Han, *Theoretical Numerical Analysis: A Functional Analysis
Framework*, 3rd edition, Lemma 7.1.4. -/
theorem ae_eq {w₁ w₂ : E → F} (h₁ : HasWeakIteratedLineDerivOn y f w₁ Ω μ)
    (h₂ : HasWeakIteratedLineDerivOn y f w₂ Ω μ) : ∀ᵐ x ∂μ, x ∈ (Ω : Set E) → w₁ x = w₂ x := by
  have key : ∀ᵐ x ∂μ, x ∈ (Ω : Set E) → w₁ x - w₂ x = 0 := by
    refine Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (LocallyIntegrableOn.sub h₁.locallyIntegrableOn_weakDeriv
        h₂.locallyIntegrableOn_weakDeriv) fun g hg h'g hgs ↦ ?_
    set φ : 𝓓(Ω, ℝ) := ⟨g, hg, h'g, hgs⟩ with hφ
    have e1 : Integrable (fun x ↦ g x • w₁ x) μ := h₁.integrable_smul_weakDeriv φ
    have e2 : Integrable (fun x ↦ g x • w₂ x) μ := h₂.integrable_smul_weakDeriv φ
    have key : ∫ x, g x • w₁ x ∂μ = ∫ x, g x • w₂ x ∂μ :=
      smul_right_injective F (pow_ne_zero n (by norm_num : (-1 : ℝ) ≠ 0))
        ((h₁.integral_smul_eq' φ).symm.trans (h₂.integral_smul_eq' φ))
    have hsub : (fun x ↦ g x • (w₁ x - w₂ x)) = fun x ↦ g x • w₁ x - g x • w₂ x :=
      funext fun x ↦ smul_sub _ _ _
    rw [hsub, integral_sub e1 e2, key, sub_self]
  filter_upwards [key] with x hx hxΩ using sub_eq_zero.mp (hx hxΩ)

/-- Along a tuple of length `0` the weak derivative agrees almost everywhere on `Ω` with the
function itself. -/
theorem ae_eq_of_length_eq_zero (hn : n = 0) (h : HasWeakIteratedLineDerivOn y f w Ω μ) :
    ∀ᵐ x ∂μ, x ∈ (Ω : Set E) → w x = f x :=
  h.ae_eq (of_length_eq_zero hn y h.locallyIntegrableOn)

end HasWeakIteratedLineDerivOn

end Line

/-! ### Weak derivatives under a continuous linear map -/

/-- **A continuous linear map passes through the weak derivative**: if `w` is a weak derivative of
`f` along the tuple `y` of directions on `Ω`, then `L ∘ w` is one of `L ∘ f`. Both sides of the
integration by parts formula integrate integrable functions, so `L` commutes with the integrals,
and `L` is `ℝ`-linear, so it commutes with the scalars `∂^n φ x` and `(-1)^n` as well. Completeness
of `F` is what makes `MeasureTheory.integral` on `F` the Bochner integral rather than the junk
value `0`, so without it the hypothesis carries no information; no completeness is needed of `G`,
where the junk value makes the conclusion trivial. -/
theorem HasWeakIteratedLineDerivOn.comp_continuousLinearMap {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {n : ℕ} {y : Fin n → E} {f w : E → F} {Ω : Opens E} {μ : Measure E}
    (h : HasWeakIteratedLineDerivOn y f w Ω μ) (L : F →L[ℝ] G) :
    HasWeakIteratedLineDerivOn y (fun x ↦ L (f x)) (fun x ↦ L (w x)) Ω μ where
  locallyIntegrableOn := h.locallyIntegrableOn.comp_continuousLinearMap L
  locallyIntegrableOn_weakDeriv := h.locallyIntegrableOn_weakDeriv.comp_continuousLinearMap L
  integral_smul_eq φ := by
    by_cases hG : CompleteSpace G
    · have i₁ : Integrable (fun x ↦ iteratedFDeriv ℝ n (φ : E → ℝ) x y • f x)
          (μ.restrict (Ω : Set E)) := by
        have h' := (h.integrable_smul (φ.iteratedFDerivApply n y)).integrableOn (s := (Ω : Set E))
        simp only [TestFunction.iteratedFDerivApply_apply] at h'
        exact h'
      have i₂ : Integrable (fun x ↦ (φ : E → ℝ) x • w x) (μ.restrict (Ω : Set E)) :=
        (h.integrable_smul_weakDeriv φ).integrableOn
      calc ∫ x in (Ω : Set E), iteratedFDeriv ℝ n (φ : E → ℝ) x y • L (f x) ∂μ
          = ∫ x in (Ω : Set E), L (iteratedFDeriv ℝ n (φ : E → ℝ) x y • f x) ∂μ := by
            simp only [map_smul]
        _ = L (∫ x in (Ω : Set E), iteratedFDeriv ℝ n (φ : E → ℝ) x y • f x ∂μ) :=
            L.integral_comp_comm i₁
        _ = L ((-1 : ℝ) ^ n • ∫ x in (Ω : Set E), (φ : E → ℝ) x • w x ∂μ) := by
            rw [h.integral_smul_eq φ]
        _ = (-1 : ℝ) ^ n • ∫ x in (Ω : Set E), (φ : E → ℝ) x • L (w x) ∂μ := by
            rw [map_smul, ← L.integral_comp_comm i₂]
            simp only [map_smul]
    · simp only [integral_of_not_completeSpace hG, smul_zero]

/-! ### The real and the complex form of one weak derivative -/

/-- **A real function has a real weak derivative exactly when its complexification has the
complexified one**: composing with the embedding `ℝ → ℂ` and with the real part, both continuous
`ℝ`-linear maps, takes each statement to the other. -/
theorem HasWeakIteratedLineDerivOn.ofReal_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [OpensMeasurableSpace E] {n : ℕ} {y : Fin n → E} {f w : E → ℝ}
    {Ω : Opens E} {μ : Measure E} :
    HasWeakIteratedLineDerivOn y f w Ω μ ↔
      HasWeakIteratedLineDerivOn y (fun x ↦ (f x : ℂ)) (fun x ↦ (w x : ℂ)) Ω μ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa using h.comp_continuousLinearMap Complex.ofRealCLM
  · simpa using h.comp_continuousLinearMap Complex.reCLM

/-! ### Classical derivatives are weak derivatives -/

section Classical

variable [FiniteDimensional ℝ E] [BorelSpace E] {N : ℕ∞ω} {m : ℕ}

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The derivatives of order at most `N` of a `C^N` function on an open set are continuous
there. -/
theorem ContDiffOn.continuousOn_iteratedFDeriv (hf : ContDiffOn ℝ N f Ω)
    (hm : (m : ℕ∞ω) ≤ N) : ContinuousOn (iteratedFDeriv ℝ m f) (Ω : Set E) := fun x hx ↦
  ((hf.contDiffAt (Ω.isOpen.mem_nhds hx)).iteratedFDeriv_right (m := 0)
    (by simpa using hm)).continuousAt.continuousWithinAt

/-- The derivatives of order at most `N` of a `C^N` function on an open set, evaluated at a fixed
tuple of directions, are locally integrable there. -/
theorem ContDiffOn.locallyIntegrableOn_iteratedFDeriv_apply [IsLocallyFiniteMeasure μ]
    (hf : ContDiffOn ℝ N f Ω) (hm : (m : ℕ∞ω) ≤ N) (y : Fin m → E) :
    LocallyIntegrableOn (fun x ↦ iteratedFDeriv ℝ m f x y) (Ω : Set E) μ :=
  ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin m ↦ E) F y).continuous.comp_continuousOn
    (hf.continuousOn_iteratedFDeriv hm)).locallyIntegrableOn Ω.isOpen.measurableSet

variable [μ.IsAddHaarMeasure]

/-- **Iterated integration by parts on an open set**: if `f` is of class `C^N` on the open set `Ω`
and `φ` is a test function on `Ω`, then for every `n ≤ N` and every tuple `y` of `n` directions,
`∫_Ω (∂^n φ) y • f = (-1)^n ∫_Ω φ • (∂^n f) y`. This is formula (7.1.1) of Atkinson and Han,
*Theoretical Numerical Analysis: A Functional Analysis Framework*, 3rd edition, §7.1. -/
theorem ContDiffOn.integral_iteratedFDeriv_smul (hf : ContDiffOn ℝ N f Ω) :
    ∀ (n : ℕ), (n : ℕ∞ω) ≤ N → ∀ (φ : 𝓓(Ω, ℝ)) (y : Fin n → E),
      ∫ x in (Ω : Set E), iteratedFDeriv ℝ n φ x y • f x ∂μ
        = (-1 : ℝ) ^ n • ∫ x in (Ω : Set E), φ x • iteratedFDeriv ℝ n f x y ∂μ := by
  intro n
  induction n with
  | zero => intro _ φ y; simp
  | succ n ih =>
    intro hn φ y
    have hnN : (n : ℕ∞ω) ≤ N := le_trans (by exact_mod_cast n.le_succ) hn
    have hn1 : (1 : ℕ∞ω) + (n : ℕ∞ω) ≤ N := by
      refine le_trans (le_of_eq ?_) hn
      push_cast
      exact add_comm _ _
    have hdiff : ∀ x ∈ (Ω : Set E), DifferentiableAt ℝ (iteratedFDeriv ℝ n f) x := fun x hx ↦
      ((hf.contDiffAt (Ω.isOpen.mem_nhds hx)).iteratedFDeriv_right (m := 1)
        hn1).differentiableAt one_ne_zero
    have hGdiff : ∀ x ∈ (Ω : Set E),
        DifferentiableAt ℝ (fun z ↦ iteratedFDeriv ℝ n f z (Fin.tail y)) x := fun x hx ↦
      ((hdiff x hx).hasFDerivAt.continuousMultilinear_apply_const _).differentiableAt
    have hGderiv : ∀ x ∈ (Ω : Set E),
        fderiv ℝ (fun z ↦ iteratedFDeriv ℝ n f z (Fin.tail y)) x (y 0)
          = iteratedFDeriv ℝ (n + 1) f x y :=
      fun x hx ↦ (iteratedFDeriv_succ_apply_left_of_differentiableAt (hdiff x hx) y).symm
    have hGloc : LocallyIntegrableOn (fun x ↦ iteratedFDeriv ℝ n f x (Fin.tail y))
        (Ω : Set E) μ := hf.locallyIntegrableOn_iteratedFDeriv_apply hnN _
    have hG'loc : LocallyIntegrableOn
        (fun x ↦ fderiv ℝ (fun z ↦ iteratedFDeriv ℝ n f z (Fin.tail y)) x (y 0)) (Ω : Set E) μ :=
      LocallyIntegrableOn.congr ((ae_restrict_iff' Ω.isOpen.measurableSet).2
        (Filter.Eventually.of_forall fun x hx ↦ (hGderiv x hx).symm))
        (hf.locallyIntegrableOn_iteratedFDeriv_apply hn y)
    have ibp : ∫ x, φ x • fderiv ℝ (fun z ↦ iteratedFDeriv ℝ n f z (Fin.tail y)) x (y 0) ∂μ
        = -∫ x, fderiv ℝ (φ : E → ℝ) x (y 0) • iteratedFDeriv ℝ n f x (Fin.tail y) ∂μ :=
      integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
        (LocallyIntegrableOn.integrable_smul_left_of_tsupport_subset hGloc
          (φ.fderivApply (y 0)).contDiff.continuous (φ.fderivApply (y 0)).hasCompactSupport
          (φ.fderivApply (y 0)).tsupport_subset)
        (LocallyIntegrableOn.integrable_smul_left_of_tsupport_subset hG'loc φ.contDiff.continuous
          φ.hasCompactSupport φ.tsupport_subset)
        (LocallyIntegrableOn.integrable_smul_left_of_tsupport_subset hGloc φ.contDiff.continuous
          φ.hasCompactSupport φ.tsupport_subset)
        (fun x _ ↦ φ.contDiff.differentiable (by simp) x)
        (fun x hx ↦ hGdiff x (φ.tsupport_subset hx))
    have r1 : ∫ x in (Ω : Set E),
          φ x • fderiv ℝ (fun z ↦ iteratedFDeriv ℝ n f z (Fin.tail y)) x (y 0) ∂μ
        = ∫ x, φ x • fderiv ℝ (fun z ↦ iteratedFDeriv ℝ n f z (Fin.tail y)) x (y 0) ∂μ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
        rw [φ.eq_zero_of_notMem hx, zero_smul]
    have r2 : ∫ x in (Ω : Set E),
          fderiv ℝ (φ : E → ℝ) x (y 0) • iteratedFDeriv ℝ n f x (Fin.tail y) ∂μ
        = ∫ x, fderiv ℝ (φ : E → ℝ) x (y 0) • iteratedFDeriv ℝ n f x (Fin.tail y) ∂μ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
        rw [show fderiv ℝ (φ : E → ℝ) x (y 0) = 0 from
          (φ.fderivApply (y 0)).eq_zero_of_notMem hx, zero_smul]
    have main : ∫ x in (Ω : Set E),
          fderiv ℝ (φ : E → ℝ) x (y 0) • iteratedFDeriv ℝ n f x (Fin.tail y) ∂μ
        = -∫ x in (Ω : Set E), φ x • iteratedFDeriv ℝ (n + 1) f x y ∂μ := by
      rw [r2, ← neg_neg (∫ x, fderiv ℝ (φ : E → ℝ) x (y 0) •
        iteratedFDeriv ℝ n f x (Fin.tail y) ∂μ), ← ibp, ← r1]
      congr 1
      exact setIntegral_congr_fun Ω.isOpen.measurableSet fun x hx ↦ by rw [hGderiv x hx]
    have e2 := ih hnN (φ.fderivApply (y 0)) (Fin.tail y)
    simp only [TestFunction.fderivApply_coe] at e2
    calc ∫ x in (Ω : Set E), iteratedFDeriv ℝ (n + 1) (φ : E → ℝ) x y • f x ∂μ
        = ∫ x in (Ω : Set E),
            iteratedFDeriv ℝ n (fun z ↦ fderiv ℝ (φ : E → ℝ) z (y 0)) x (Fin.tail y) • f x ∂μ :=
          setIntegral_congr_fun Ω.isOpen.measurableSet fun x _ ↦ by
            rw [ContDiff.iteratedFDeriv_succ_apply_left' φ.contDiff n y x]
      _ = (-1 : ℝ) ^ n • ∫ x in (Ω : Set E),
            fderiv ℝ (φ : E → ℝ) x (y 0) • iteratedFDeriv ℝ n f x (Fin.tail y) ∂μ := e2
      _ = (-1 : ℝ) ^ n • -∫ x in (Ω : Set E), φ x • iteratedFDeriv ℝ (n + 1) f x y ∂μ := by
          rw [main]
      _ = (-1 : ℝ) ^ (n + 1) • ∫ x in (Ω : Set E), φ x • iteratedFDeriv ℝ (n + 1) f x y ∂μ := by
          rw [pow_succ, mul_smul, neg_one_smul]

/-- **A classical derivative is a weak derivative**: Atkinson and Han, *Theoretical Numerical
Analysis: A Functional Analysis Framework*, 3rd edition, Lemma 7.1.5. So the weak derivative
extends the classical one, and it is natural to write both `∂^n`. -/
theorem ContDiffOn.hasWeakIteratedFDerivOn (hf : ContDiffOn ℝ N f Ω) (hm : (m : ℕ∞ω) ≤ N) :
    HasWeakIteratedFDerivOn m f (iteratedFDeriv ℝ m f) Ω μ where
  locallyIntegrableOn := hf.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  locallyIntegrableOn_weakDeriv :=
    (hf.continuousOn_iteratedFDeriv hm).locallyIntegrableOn Ω.isOpen.measurableSet
  integral_smul_eq φ y := hf.integral_iteratedFDeriv_smul m hm φ y

end Classical

/-! ### First-order weak derivatives -/

section FirstOrder

variable {w : E → E →L[ℝ] F}

/-- Unfolding of `HasWeakFDerivOn`: local integrability of the function and of its weak
derivative, and the first-order integration by parts formula. -/
theorem hasWeakFDerivOn_iff :
    HasWeakFDerivOn f w Ω μ ↔ LocallyIntegrableOn f Ω μ ∧ LocallyIntegrableOn w Ω μ ∧
      ∀ (φ : 𝓓(Ω, ℝ)) (v : E), ∫ x in (Ω : Set E), fderiv ℝ φ x v • f x ∂μ
        = -∫ x in (Ω : Set E), φ x • w x v ∂μ := by
  constructor
  · refine fun h ↦ ⟨h.locallyIntegrableOn, ?_, fun φ v ↦ ?_⟩
    · refine MeasureTheory.LocallyIntegrableOn.congr
        (Filter.Eventually.of_forall fun x ↦ ?_)
        (MeasureTheory.LocallyIntegrableOn.comp_continuousLinearMap
          h.locallyIntegrableOn_weakDeriv
          (continuousMultilinearCurryFin1 ℝ E F).toContinuousLinearEquiv.toContinuousLinearMap)
      simp
    · simpa [iteratedFDeriv_one_apply] using h.integral_smul_eq φ fun _ ↦ v
  · refine fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, ?_, fun φ y ↦ ?_⟩
    · exact MeasureTheory.LocallyIntegrableOn.comp_continuousLinearMap h₂
        (continuousMultilinearCurryFin1 ℝ E F).symm.toContinuousLinearEquiv.toContinuousLinearMap
    · simpa [iteratedFDeriv_one_apply] using h₃ φ (y 0)

/-- The integration by parts formula defining a first-order weak derivative. -/
theorem HasWeakFDerivOn.integral_smul_eq (h : HasWeakFDerivOn f w Ω μ) (φ : 𝓓(Ω, ℝ)) (v : E) :
    ∫ x in (Ω : Set E), fderiv ℝ φ x v • f x ∂μ = -∫ x in (Ω : Set E), φ x • w x v ∂μ :=
  (hasWeakFDerivOn_iff.1 h).2.2 φ v

/-- A function with a first-order weak derivative is locally integrable. -/
theorem HasWeakFDerivOn.locallyIntegrableOn (h : HasWeakFDerivOn f w Ω μ) :
    LocallyIntegrableOn f Ω μ :=
  (hasWeakFDerivOn_iff.1 h).1

/-- A first-order weak derivative is locally integrable. -/
theorem HasWeakFDerivOn.locallyIntegrableOn_weakDeriv (h : HasWeakFDerivOn f w Ω μ) :
    LocallyIntegrableOn w Ω μ :=
  (hasWeakFDerivOn_iff.1 h).2.1

end FirstOrder
