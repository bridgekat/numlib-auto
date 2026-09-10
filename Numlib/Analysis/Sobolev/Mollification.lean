/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Mollification`, beside
`Mathlib.Analysis.Distribution.WeakDeriv`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Convolution.Lp
import Numlib.Analysis.Sobolev.WeakDeriv

/-!
# Mollification on an open set

Convolving a function with a smooth bump `φ` supported in the closed ball of radius `ε` smooths it,
at the cost of moving information a distance `ε`. On an open set `Ω` that cost is a *domain*
restriction: `(φ ⋆ f) x` depends on `f` only on `closedBall x ε`, so it is defined as soon as that
ball lies in `Ω`, and it is only on the `ε`-erosion of `Ω` that the mollification is available at
all. This file develops that bookkeeping, and proves the fact everything downstream rests on:

**the weak derivative commutes with mollification**, `∂^y (φ ⋆ f) = φ ⋆ (∂^y f)` at every point
whose closed `ε`-ball lies in `Ω`.

For the classical statements see for instance L. C. Evans, *Partial Differential Equations*, 2nd
edition, American Mathematical Society, 2010, §C.5 and §5.3.1, or H. Brezis, *Functional Analysis,
Sobolev Spaces and Partial Differential Equations*, Springer, 2011, §4.4 and §9.1.

## Main results

* `exists_isCompact_forall_closedBall_subset` and `IsCompact.exists_pos_forall_closedBall_subset`:
  the two forms of "a compact set sits at a positive distance from the complement of an open set
  that contains it", which is the hypothesis every statement below needs.
* `ContDiff.iteratedFDeriv_comp_const_sub`: the iterated derivative of the reflected translate
  `z ↦ f (a - z)` is `(-1) ^ n` times that of `f` at `a - z`. The tuple of directions is *not*
  reversed; see the implementation notes.
* `TestFunction.compConstSub`: the reflected translate of a bump, bundled as a test function on
  `Ω`. This is what turns a convolution into an instance of the defining identity of the weak
  derivative.
* `MeasureTheory.LocallyIntegrable.iteratedFDeriv_convolution_left_apply`: differentiating a
  convolution moves the derivative onto the smooth factor, at every order.
* `HasWeakIteratedLineDerivOn.convolution_iteratedFDeriv`: the identity
  `(∂^y φ) ⋆ f = φ ⋆ (∂^y f)`, an integration by parts under the integral sign and nothing more.
* `HasWeakIteratedLineDerivOn.iteratedFDeriv_convolution` and
  `HasWeakIteratedFDerivOn.iteratedFDeriv_convolution`: **the commutation of the weak derivative
  with mollification**, in the tuple-by-tuple and the bundled readings.
* `HasWeakIteratedLineDerivOn.exists_seq_contDiff_tendsto_eLpNorm`: **local approximation in
  `W^{k,p}`**, the mollifications of `f` converge to `f` and their classical derivatives to the
  weak derivative of `f`, in `L^p` of a relatively compact open subset of `Ω`.
* `HasWeakIteratedLineDerivOn.mul`: **the product rule** for two factors that are merely locally
  integrable, with conjugate exponents.
* `HasWeakIteratedLineDerivOn.contDiff_comp`: **the chain rule** against a `C^1` function with
  bounded derivative.
* `TopologicalSpace.Opens.exists_exhaustion` and `IsCompact.exists_contDiff_eqOn_one`: an
  exhaustion of an open set by relatively compact opens, and the smooth Urysohn lemma. Neither is
  used here; both are tools that the density theorems built on this file will need, and neither
  exists in Mathlib in the vector-space namespace.

## Implementation notes

The reflection step is the one that looks dangerous and is not. `iteratedFDeriv ℝ n` of
`z ↦ φ (a - z)` is computed by writing that function as `(fun w ↦ φ (a + w)) ∘ (-id)` and applying
`ContinuousLinearMap.iteratedFDeriv_comp_right`, which composes the derivative with the linear map
in *every* slot; since `-id` contributes the same scalar `-1` in each slot, multilinearity turns
the whole thing into `(-1) ^ n` and the directions come out in their original order. In particular
no reversal of the tuple appears, unlike in the `iteratedFDeriv_succ_apply_left` versus
`iteratedFDeriv_succ_apply_right` bookkeeping that `Numlib/Analysis/Sobolev/WeakDeriv.lean` warns
about.

`HasWeakIteratedLineDerivOn` asks for local integrability on `Ω` only, so `φ ⋆ f` need not be
defined, let alone smooth, away from the erosion of `Ω`. Both places where that matters are handled
by truncation: `f` is replaced by `K.indicator f` for a compact `K ⊆ Ω` chosen to contain
`closedBall x' ε` for every `x'` in a neighbourhood of the point in question, which is globally
integrable and hence has a globally smooth mollification, and which agrees with `f` wherever the
convolution can see it. `Filter.EventuallyEq.iteratedFDeriv` then transfers the derivative, because
an iterated derivative at a point depends only on the germ there.

The product and chain rules at the end are the two consumers of the local approximation theorem,
and they illustrate the two ways a limit can be taken. The product rule pairs an `L^p` convergence
against a fixed `L^q` factor, so Hölder's inequality does all the work
(`MeasureTheory.tendsto_integral_mul_of_tendsto_eLpNorm`). The chain rule cannot: the factor
`f' ∘ v_ε` moves with `ε` and converges only pointwise, so one term needs an almost-everywhere
convergent subsequence (`MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae`) and the dominated
convergence theorem. Extracting that subsequence is harmless because the statement being proved is
an identity between two fixed quantities.
-/

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Convolution Distributions ENNReal Manifold Topology

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E} {n : ℕ}

/-! ### Compact sets inside an open set

Everything below needs a positive distance between a compact set and the complement of an open set
containing it, in one of two shapes: a compact `K ⊆ Ω` that swallows `closedBall x' ε` for every
`x'` near a given point, or a positive `ε` that works uniformly on a neighbourhood of a given
compact set. -/

section Neighbourhoods

variable [FiniteDimensional ℝ E]

/-- A point whose closed `ε`-ball lies in an open set `U` has a neighbourhood on which that stays
true *uniformly*, inside a single compact subset of `U`: there are a compact `K ⊆ U` and a `δ > 0`
with `closedBall x' ε ⊆ K` for every `x'` in the ball of radius `δ` about `x`. This is what lets a
function that is only locally integrable on `U` be truncated to a globally integrable one without
the convolution noticing. -/
theorem exists_isCompact_forall_closedBall_subset {U : Set E} (hU : IsOpen U)
    {ε : ℝ} {x : E} (hx : closedBall x ε ⊆ U) :
    ∃ (K : Set E) (δ : ℝ), IsCompact K ∧ K ⊆ U ∧ 0 < δ ∧ closedBall x ε ⊆ interior K ∧
      ∀ x' ∈ ball x δ, closedBall x' ε ⊆ K := by
  obtain ⟨r, hr, hrU⟩ := (isCompact_closedBall x ε).exists_thickening_subset_open hU hx
  refine ⟨cthickening (r / 2) (closedBall x ε), r / 2, (isCompact_closedBall x ε).cthickening,
    (cthickening_subset_thickening' hr (by linarith) _).trans hrU, by linarith, ?_, ?_⟩
  · exact (self_subset_thickening (by linarith) _).trans
      (thickening_subset_interior_cthickening _ _)
  · intro x' hx' p hp
    refine mem_cthickening_of_dist_le p (p - (x' - x)) _ _ ?_ ?_
    · simp only [mem_closedBall, dist_eq_norm] at hp ⊢
      simpa [sub_sub, sub_add_eq_sub_sub] using hp
    · rw [mem_ball, dist_eq_norm] at hx'
      rw [dist_eq_norm, show p - (p - (x' - x)) = x' - x by abel]
      exact hx'.le

/-- A compact subset `K` of an open set `U` has an open neighbourhood `V`, still relatively compact
in `U`, and a radius `ε > 0` such that `closedBall x ε ⊆ U` for every `x ∈ V`. This is the domain
`V ⋐ U` on which mollification at scale `ε` is available. -/
theorem IsCompact.exists_pos_forall_closedBall_subset {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (V : Set E) (ε : ℝ), IsOpen V ∧ K ⊆ V ∧ 0 < ε ∧ IsCompact (closure V) ∧ closure V ⊆ U ∧
      ∀ x ∈ V, closedBall x ε ⊆ U := by
  obtain ⟨r, hr, hrU⟩ := hK.exists_thickening_subset_open hU hKU
  refine ⟨thickening (r / 3) K, r / 3, isOpen_thickening, self_subset_thickening (by linarith) K,
    by linarith, ?_, ?_, ?_⟩
  · exact hK.cthickening.of_isClosed_subset isClosed_closure
      (closure_minimal (thickening_subset_cthickening _ _) isClosed_cthickening)
  · refine (closure_minimal (thickening_subset_cthickening _ _) isClosed_cthickening).trans ?_
    exact (cthickening_subset_thickening' hr (by linarith) _).trans hrU
  · intro x hx p hp
    refine hrU ?_
    rw [mem_thickening_iff] at hx ⊢
    obtain ⟨z, hz, hxz⟩ := hx
    refine ⟨z, hz, ?_⟩
    have h := dist_triangle p x z
    rw [mem_closedBall] at hp
    linarith

end Neighbourhoods

/-! ### Exhaustions and smooth cut-offs

Two facts about an open subset of a finite-dimensional real normed space that Mathlib has only for
a whole space (`CompactExhaustion`) or only on a manifold (`SmoothPartitionOfUnity`). They are not
used in this file; they are the pieces that a density theorem built on the mollification below
needs, and are recorded here so that they exist under findable names. -/

section Exhaustion

variable [FiniteDimensional ℝ E]

/-- **An open set is exhausted by relatively compact open subsets**: there is a sequence of open
sets `U 0, U 1, …`, each with compact closure contained in the next, whose union is `Ω`. Mathlib's
`CompactExhaustion` does this for a whole space; this is the version for an open subset, and the
point of the proof is that neither `SigmaCompactSpace ↥Ω` nor `WeaklyLocallyCompactSpace ↥Ω` is
found by instance search, so `IsOpen.locallyCompactSpace` has to be supplied by hand. -/
theorem TopologicalSpace.Opens.exists_exhaustion (Ω : Opens E) :
    ∃ U : ℕ → Opens E, (∀ n, IsCompact (closure (U n : Set E))) ∧
      (∀ n, closure (U n : Set E) ⊆ U (n + 1)) ∧ (⋃ n, (U n : Set E)) = Ω := by
  have := Ω.isOpen.locallyCompactSpace
  set K : CompactExhaustion (Ω : Set E) := default with hK
  set V : ℕ → Set E := fun n ↦ Subtype.val '' interior (K (n + 1)) with hV
  have hopen : ∀ n, IsOpen (V n) := fun n ↦ Ω.isOpen.isOpenMap_subtype_val _ isOpen_interior
  have hcpt : ∀ n, IsCompact (Subtype.val '' (K (n + 1) : Set (Ω : Set E))) := fun n ↦
    (K.isCompact (n + 1)).image continuous_subtype_val
  have hsub : ∀ n, closure (V n) ⊆ Subtype.val '' (K (n + 1) : Set (Ω : Set E)) := fun n ↦
    closure_minimal (image_mono interior_subset) (hcpt n).isClosed
  refine ⟨fun n ↦ ⟨V n, hopen n⟩, fun n ↦ ?_, fun n ↦ ?_, ?_⟩
  · exact (hcpt n).of_isClosed_subset isClosed_closure (hsub n)
  · exact (hsub n).trans (image_mono (K.subset_interior (by omega)))
  · apply subset_antisymm
    · exact iUnion_subset fun n ↦ (image_subset_range _ _).trans (by simp)
    · rintro x hx
      obtain ⟨n, hn⟩ := K.exists_mem ⟨x, hx⟩
      exact mem_iUnion.2 ⟨n, ⟨x, hx⟩, K.subset_interior_succ n hn, rfl⟩

/-- **The smooth Urysohn lemma** on a finite-dimensional real normed space: a compact set `K`
inside an open set `V` carries a smooth function that is `1` on `K`, is supported in `V`, and takes
values in `[0, 1]`. Mathlib proves this on a manifold, as
`exists_contMDiffMap_zero_one_nhds_of_isClosed`; this is the vector-space reading, at `M = E` and
`I = 𝓘(ℝ, E)`. -/
theorem IsCompact.exists_contDiff_eqOn_one {K V : Set E} (hK : IsCompact K) (hV : IsOpen V)
    (hKV : K ⊆ V) :
    ∃ f : E → ℝ, ContDiff ℝ ∞ f ∧ EqOn f 1 K ∧ tsupport f ⊆ V ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨f, hf0, hf1, hf01⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed (I := 𝓘(ℝ, E)) (n := (⊤ : ℕ∞))
      hV.isClosed_compl hK.isClosed (disjoint_compl_left_iff_subset.2 hKV)
  refine ⟨f, contMDiff_iff_contDiff.mp f.contMDiff, fun x hx ↦ hf1.self_of_nhdsSet x hx, ?_, hf01⟩
  obtain ⟨W, hWopen, hWsub, hWf⟩ := mem_nhdsSet_iff_exists.1 hf0
  have : tsupport (f : E → ℝ) ⊆ Wᶜ :=
    closure_minimal (fun x hx hxW ↦ hx (hWf hxW)) hWopen.isClosed_compl
  exact this.trans (compl_subset_comm.2 hWsub)

end Exhaustion

/-! ### The iterated derivative of a reflected translate -/

section Reflection

/-- **The iterated derivative of a reflected translate.** For `f` of class `C^N` and `n ≤ N`, the
`n`-th derivative of `z ↦ f (a - z)` is `(-1) ^ n` times the `n`-th derivative of `f` at `a - x`,
evaluated at the *same* tuple of directions: reflecting the argument contributes one sign per slot
and does nothing else. -/
theorem ContDiff.iteratedFDeriv_comp_const_sub {N : ℕ∞ω} {f : E → F} (hf : ContDiff ℝ N f)
    (hn : (n : ℕ∞ω) ≤ N) (a x : E) (y : Fin n → E) :
    iteratedFDeriv ℝ n (fun z ↦ f (a - z)) x y
      = (-1 : ℝ) ^ n • iteratedFDeriv ℝ n f (a - x) y := by
  have hg : ContDiff ℝ N (fun w ↦ f (a + w)) := hf.comp (contDiff_const.add contDiff_id)
  have h1 : (fun z : E ↦ f (a - z))
      = (fun w ↦ f (a + w)) ∘ ⇑(-ContinuousLinearMap.id ℝ E) := by
    funext z; simp [sub_eq_add_neg]
  rw [h1, ContinuousLinearMap.iteratedFDeriv_comp_right (-ContinuousLinearMap.id ℝ E) hg x hn]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, neg_apply,
    ContinuousLinearMap.id_apply]
  rw [show (fun i ↦ -(y i)) = fun i ↦ (-1 : ℝ) • y i by funext i; simp,
    ContinuousMultilinearMap.map_smul_univ]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 2
  rw [iteratedFDeriv_comp_add_left]
  congr 1
  rw [sub_eq_add_neg]

end Reflection

/-! ### The reflected translate of a bump, as a test function -/

namespace TestFunction

variable [FiniteDimensional ℝ E]

/-- The reflected translate `z ↦ φ (x - z)` of a smooth function `φ` supported in the closed ball
of radius `ε` about the origin, as a test function on `Ω`. The hypothesis `closedBall x ε ⊆ Ω` is
exactly what makes the support land inside `Ω`.

This is the bridge between the convolution `(φ ⋆ f) x = ∫ φ t • f (x - t)` and the defining
identity of the weak derivative on `Ω`, which quantifies over test functions on `Ω`. -/
def compConstSub (Ω : Opens E) {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) {ε : ℝ}
    (hsupp : tsupport φ ⊆ closedBall 0 ε) {x : E} (hx : closedBall x ε ⊆ (Ω : Set E)) :
    𝓓(Ω, ℝ) where
  toFun z := φ (x - z)
  contDiff' := hφ.comp (contDiff_const.sub contDiff_id)
  hasCompactSupport' := by
    refine IsCompact.of_isClosed_subset (isCompact_closedBall x ε) isClosed_closure ?_
    refine closure_minimal (fun z hz ↦ ?_) isClosed_closedBall
    have : x - z ∈ tsupport φ := subset_tsupport _ hz
    simpa [mem_closedBall, dist_eq_norm, norm_sub_rev] using hsupp this
  tsupport_subset' := by
    refine subset_trans (closure_minimal (fun z hz ↦ ?_) isClosed_closedBall) hx
    have : x - z ∈ tsupport φ := subset_tsupport _ hz
    simpa [mem_closedBall, dist_eq_norm, norm_sub_rev] using hsupp this

/-- `TestFunction.compConstSub` as a function. -/
@[simp]
theorem compConstSub_coe (Ω : Opens E) {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) {ε : ℝ}
    (hsupp : tsupport φ ⊆ closedBall 0 ε) {x : E} (hx : closedBall x ε ⊆ (Ω : Set E)) :
    (compConstSub Ω hφ hsupp hx : E → ℝ) = fun z ↦ φ (x - z) :=
  rfl

end TestFunction

/-! ### Derivatives of a convolution

The first-order statement `MeasureTheory.LocallyIntegrable.fderiv_convolution_left_apply` and the
existence criterion `MeasureTheory.LocallyIntegrableOn.convolutionExistsAt` are in
`Numlib/Analysis/Convolution/Lp.lean`; the iterated form stays here because its induction runs on
`ContDiff.iteratedFDeriv_succ_apply_left'` of `Numlib/Analysis/Sobolev/WeakDeriv.lean`, which that
file does not import. -/

section Convolution

variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [MeasurableSpace E] [FiniteDimensional ℝ E]
  [BorelSpace E] [CompleteSpace F] {μ : Measure E} [μ.IsAddHaarMeasure]
  {L : E₁ →L[ℝ] E₂ →L[ℝ] F} {g : E → E₂}

omit [CompleteSpace F] in
/-- Differentiating a convolution `n` times along a tuple of directions moves all `n` derivatives
onto the smooth, compactly supported factor. -/
theorem MeasureTheory.LocallyIntegrable.iteratedFDeriv_convolution_left_apply
    (hg : LocallyIntegrable g μ) :
    ∀ (n : ℕ) {φ : E → E₁}, HasCompactSupport φ → ContDiff ℝ ∞ φ → ∀ (x : E) (y : Fin n → E),
      _root_.iteratedFDeriv ℝ n (φ ⋆[L, μ] g) x y
        = ((fun z ↦ _root_.iteratedFDeriv ℝ n φ z y) ⋆[L, μ] g) x := by
  intro n
  induction n with
  | zero => intro φ _ _ x y; simp [iteratedFDeriv_zero_apply]
  | succ n ih =>
    intro φ hcφ hφ x y
    have hconv : ContDiff ℝ ∞ (φ ⋆[L, μ] g) := hcφ.contDiff_convolution_left L hφ hg
    set ψ : E → E₁ := fun t ↦ fderiv ℝ φ t (y 0) with hψ
    have hψc : ContDiff ℝ ∞ ψ := (hφ.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
    have hψs : HasCompactSupport ψ := hcφ.fderiv_apply ℝ (y 0)
    have hfun : (fun z ↦ fderiv ℝ (φ ⋆[L, μ] g) z (y 0)) = ψ ⋆[L, μ] g :=
      funext fun z ↦ hg.fderiv_convolution_left_apply hcφ hφ z (y 0)
    rw [hconv.iteratedFDeriv_succ_apply_left' n y x, hfun, ih hψs hψc x (Fin.tail y)]
    exact congrArg (fun h ↦ (h ⋆[L, μ] g) x)
      (funext fun z ↦ (hφ.iteratedFDeriv_succ_apply_left' n y z).symm)

end Convolution

/-! ### The weak derivative commutes with mollification -/

section Commutation

open ContinuousLinearMap

variable [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] {μ : Measure E}
  [μ.IsAddHaarMeasure] {y : Fin n → E} {f w : E → F}

/-- **Integration by parts under the integral sign**: for a bump `φ` supported in the closed ball
of radius `ε`, and a point `x` with `closedBall x ε ⊆ Ω`, convolving `f` against the `n`-th
derivative of `φ` along `y` is the same as convolving the weak derivative of `f` along `y` against
`φ` itself.

This carries all the content of the commutation of the weak derivative with mollification; what
`HasWeakIteratedLineDerivOn.iteratedFDeriv_convolution` adds is only the identification of the
left-hand side with a derivative of `φ ⋆ f`. -/
theorem HasWeakIteratedLineDerivOn.convolution_iteratedFDeriv
    (h : HasWeakIteratedLineDerivOn y f w Ω μ) {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) {ε : ℝ}
    (hsupp : tsupport φ ⊆ closedBall 0 ε) {x : E} (hx : closedBall x ε ⊆ (Ω : Set E)) :
    ((fun z ↦ iteratedFDeriv ℝ n φ z y) ⋆[lsmul ℝ ℝ, μ] f) x = (φ ⋆[lsmul ℝ ℝ, μ] w) x := by
  set ψ : 𝓓(Ω, ℝ) := TestFunction.compConstSub Ω hφ hsupp hx with hψ
  have hrefl : ∀ s, iteratedFDeriv ℝ n (ψ : E → ℝ) s y
      = (-1 : ℝ) ^ n • iteratedFDeriv ℝ n φ (x - s) y := fun s ↦ by
    simpa [hψ] using hφ.iteratedFDeriv_comp_const_sub (n := n) (by simp) x s y
  have hL : ((fun z ↦ iteratedFDeriv ℝ n φ z y) ⋆[lsmul ℝ ℝ, μ] f) x
      = ∫ s, iteratedFDeriv ℝ n φ (x - s) y • f s ∂μ := by
    rw [convolution_def]
    simp only [lsmul_apply]
    rw [← integral_sub_left_eq_self (fun t ↦ iteratedFDeriv ℝ n φ (x - t) y • f t) μ x]
    exact integral_congr_ae (Eventually.of_forall fun t ↦ by simp only [sub_sub_cancel])
  have hR : (φ ⋆[lsmul ℝ ℝ, μ] w) x = ∫ s, φ (x - s) • w s ∂μ := by
    rw [convolution_def]
    simp only [lsmul_apply]
    rw [← integral_sub_left_eq_self (fun t ↦ φ (x - t) • w t) μ x]
    exact integral_congr_ae (Eventually.of_forall fun t ↦ by simp only [sub_sub_cancel])
  have key := h.integral_smul_eq' ψ
  have e1 : ∫ s, iteratedFDeriv ℝ n (ψ : E → ℝ) s y • f s ∂μ
      = (-1 : ℝ) ^ n • ∫ s, iteratedFDeriv ℝ n φ (x - s) y • f s ∂μ := by
    rw [← integral_smul]
    exact integral_congr_ae (Eventually.of_forall fun s ↦ by simp only [hrefl s, smul_assoc])
  have e2 : ∫ s, ψ s • w s ∂μ = ∫ s, φ (x - s) • w s ∂μ := rfl
  rw [e1, e2] at key
  rw [hL, hR]
  exact smul_right_injective F (pow_ne_zero n (by norm_num : (-1 : ℝ) ≠ 0)) key

/-- **The weak derivative commutes with mollification**, in the reading that fixes a tuple `y` of
directions: if `w` is the weak derivative of `f` along `y` on `Ω`, and `φ` is a smooth bump
supported in the closed ball of radius `ε`, then at every point `x` whose closed `ε`-ball lies in
`Ω` the mollification `φ ⋆ f` has classical derivative

`∂^y (φ ⋆ f) x = (φ ⋆ w) x`.

Note that `f` is assumed locally integrable on `Ω` only, so `φ ⋆ f` need not be smooth, or even
defined, elsewhere; the derivative on the left is nevertheless the honest one, because `φ ⋆ f`
agrees near `x` with the mollification of a compactly supported truncation of `f`, which is smooth
on the whole space. -/
theorem HasWeakIteratedLineDerivOn.iteratedFDeriv_convolution
    (h : HasWeakIteratedLineDerivOn y f w Ω μ) {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) {ε : ℝ}
    (hsupp : tsupport φ ⊆ closedBall 0 ε) {x : E} (hx : closedBall x ε ⊆ (Ω : Set E)) :
    iteratedFDeriv ℝ n (φ ⋆[lsmul ℝ ℝ, μ] f) x y = (φ ⋆[lsmul ℝ ℝ, μ] w) x := by
  have hcφ : HasCompactSupport φ :=
    IsCompact.of_isClosed_subset (isCompact_closedBall 0 ε) isClosed_closure hsupp
  obtain ⟨K, δ, hK, hKΩ, hδ, hxK, hball⟩ :=
    exists_isCompact_forall_closedBall_subset Ω.isOpen hx
  set f' : E → F := K.indicator f with hf'
  have hf'loc : LocallyIntegrable f' μ :=
    ((h.locallyIntegrableOn.integrableOn_compact_subset hKΩ hK).integrable_indicator
      hK.isClosed.measurableSet).locallyIntegrable
  have heq : (φ ⋆[lsmul ℝ ℝ, μ] f) =ᶠ[𝓝 x] (φ ⋆[lsmul ℝ ℝ, μ] f') := by
    filter_upwards [ball_mem_nhds x hδ] with x' hx'
    refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
    rcases eq_or_ne (φ t) 0 with h0 | h0
    · simp [h0]
    · have ht : t ∈ closedBall (0 : E) ε := hsupp (subset_tsupport _ h0)
      have hmem : x' - t ∈ K := hball x' hx' (by
        simpa [mem_closedBall, dist_eq_norm] using (by simpa using ht : ‖t‖ ≤ ε))
      simp [hf', Set.indicator_of_mem hmem]
  have h' : HasWeakIteratedLineDerivOn y f' w ⟨interior K, isOpen_interior⟩ μ :=
    (h.mono (interior_subset.trans hKΩ)).congr_ae
      (Filter.eventually_of_mem (self_mem_ae_restrict isOpen_interior.measurableSet)
        fun z hz ↦ (Set.indicator_of_mem (interior_subset hz) f).symm)
      (Filter.EventuallyEq.refl _ _)
  rw [(Filter.EventuallyEq.iteratedFDeriv ℝ heq n).self_of_nhds,
    hf'loc.iteratedFDeriv_convolution_left_apply n hcφ hφ x y,
    h'.convolution_iteratedFDeriv hφ hsupp hxK]

/-- **The weak derivative commutes with mollification**, in the bundled reading: if `w` is the
`n`-th weak derivative of `f` on `Ω` and `φ` is a smooth bump supported in the closed ball of
radius `ε`, then at every point `x` whose closed `ε`-ball lies in `Ω`,

`∂^n (φ ⋆ f) x = (φ ⋆ w) x`

as continuous `n`-linear maps. -/
theorem HasWeakIteratedFDerivOn.iteratedFDeriv_convolution {w : E → E [×n]→L[ℝ] F}
    (h : HasWeakIteratedFDerivOn n f w Ω μ) {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) {ε : ℝ}
    (hsupp : tsupport φ ⊆ closedBall 0 ε) {x : E} (hx : closedBall x ε ⊆ (Ω : Set E)) :
    iteratedFDeriv ℝ n (φ ⋆[lsmul ℝ ℝ, μ] f) x = (φ ⋆[lsmul ℝ ℝ, μ] w) x := by
  have hex : ConvolutionExistsAt φ w x (lsmul ℝ ℝ) μ :=
    h.locallyIntegrableOn_weakDeriv.convolutionExistsAt hφ.continuous hsupp hx
  refine ContinuousMultilinearMap.ext fun z ↦ ?_
  rw [(h.lineDeriv z).iteratedFDeriv_convolution hφ hsupp hx, convolution_def, convolution_def,
    ContinuousMultilinearMap.integral_apply hex]
  rfl

end Commutation

/-! ### Hölder's inequality, locally

The local form of Hölder's inequality that the product rule needs. Its `L^p`-limit companions --
`MeasureTheory.tendsto_integral_mul_of_tendsto_eLpNorm`,
`MeasureTheory.tendsto_eLpNorm_one_of_tendsto_eLpNorm` and
`MeasureTheory.enorm_integral_smul_le_of_bound` -- are in
`Numlib/Analysis/Convolution/Lp.lean`, and the `L^p` analogues of local integrability on a compact
subset are in `Numlib/Analysis/Sobolev/WeakDeriv.lean`, beside `MeasureTheory.LocallyMemLpOn`
itself. -/

namespace MeasureTheory

variable {X G : Type*} [TopologicalSpace X] [MeasurableSpace X] [NormedAddCommGroup G]
  {f : X → G} {s t : Set X} {μ : Measure X} {p : ℝ≥0∞}

/-- **Hölder's inequality, locally**: the product of a function locally in `L^p` on `s` with one
locally in `L^q` on `s`, for Hölder conjugate `p` and `q`, is locally integrable on `s`. -/
theorem LocallyMemLpOn.locallyIntegrableOn_mul {q : ℝ≥0∞} [ENNReal.HolderConjugate p q]
    {u v : X → ℝ} (hu : LocallyMemLpOn u p s μ) (hv : LocallyMemLpOn v q s μ) :
    LocallyIntegrableOn (fun x ↦ u x * v x) s μ := by
  intro x hx
  obtain ⟨a, ha, hua⟩ := hu x hx
  obtain ⟨b, hb, hvb⟩ := hv x hx
  refine ⟨a ∩ b, Filter.inter_mem ha hb, ?_⟩
  have hu' : MemLp u p (μ.restrict (a ∩ b)) :=
    hua.mono_measure (Measure.restrict_mono Set.inter_subset_left le_rfl)
  have hv' : MemLp v q (μ.restrict (a ∩ b)) :=
    hvb.mono_measure (Measure.restrict_mono Set.inter_subset_right le_rfl)
  have huv : MemLp (fun x ↦ u x * v x) 1 (μ.restrict (a ∩ b)) := MemLp.mul' hv' hu'
  exact memLp_one_iff_integrable.1 huv

end MeasureTheory

/-! ### Local approximation in `W^{k,p}` -/

section Approximation

open ContinuousLinearMap

variable [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F]
  {μ : Measure E} [μ.IsAddHaarMeasure] {y : Fin n → E} {f w : E → F} {p : ℝ≥0∞}

/-- **Local approximation in `W^{k,p}` by smooth functions.** Let `w` be the weak derivative of `f`
along a tuple `y` of directions on an open set `Ω`, with both `f` and `w` in `L^p_loc(Ω)` for some
`p < ∞`, and let `V` be an open set whose closure is a compact subset of `Ω`. Then there are
globally smooth functions `g 0, g 1, …`, themselves in `L^p(V)` together with their derivatives
`∂^y (g j)`, such that `g j → f` and `∂^y (g j) → w` in `L^p(V)`.

The `g j` are the mollifications of a compactly supported truncation of `f`; the convergence is
`ContDiffBump.tendsto_eLpNorm_convolution_sub`, and the identification of `∂^y (g j)` with the
mollification of `w` on `V` is `HasWeakIteratedLineDerivOn.iteratedFDeriv_convolution`.

This is the local, `L^p`-flavoured half of the Meyers-Serrin theorem `H = W`; what it does not do
is patch the local approximations together over an exhaustion of `Ω`. -/
theorem HasWeakIteratedLineDerivOn.exists_seq_contDiff_tendsto_eLpNorm
    (h : HasWeakIteratedLineDerivOn y f w Ω μ) (hf : LocallyMemLpOn f p Ω μ)
    (hw : LocallyMemLpOn w p Ω μ) (hp : 1 ≤ p) (hp' : p ≠ ⊤) {V : Set E} (hVo : IsOpen V)
    (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ (Ω : Set E)) :
    ∃ g : ℕ → E → F, (∀ j, ContDiff ℝ ∞ (g j)) ∧ (∀ j, MemLp (g j) p (μ.restrict V)) ∧
      (∀ j, MemLp (fun x ↦ iteratedFDeriv ℝ n (g j) x y) p (μ.restrict V)) ∧
      Tendsto (fun j ↦ eLpNorm (fun x ↦ g j x - f x) p (μ.restrict V)) atTop (𝓝 0) ∧
      Tendsto (fun j ↦ eLpNorm (fun x ↦ iteratedFDeriv ℝ n (g j) x y - w x) p (μ.restrict V))
        atTop (𝓝 0) := by
  obtain ⟨W, -, hWo, hVW, -, hWc, hWΩ, -⟩ := hVc.exists_pos_forall_closedBall_subset Ω.isOpen hVΩ
  obtain ⟨V', ε, hV'o, hVV', hε, -, -, hV'ball⟩ := hVc.exists_pos_forall_closedBall_subset hWo hVW
  set C : Set E := closure W with hCdef
  have hCmeas : MeasurableSet C := hWc.isClosed.measurableSet
  have hWC : W ⊆ interior C := interior_maximal subset_closure hWo
  have hVC : V ⊆ C := (subset_closure.trans hVW).trans subset_closure
  set f' : E → F := C.indicator f with hf'def
  set w' : E → F := C.indicator w with hw'def
  have hf'Lp : MemLp f' p μ :=
    (memLp_indicator_iff_restrict hCmeas).2 (hf.memLp_restrict_of_compact_subset hp' hWΩ hWc)
  have hw'Lp : MemLp w' p μ :=
    (memLp_indicator_iff_restrict hCmeas).2 (hw.memLp_restrict_of_compact_subset hp' hWΩ hWc)
  have hf'loc : LocallyIntegrable f' μ := hf'Lp.locallyIntegrable hp
  have hint : HasWeakIteratedLineDerivOn y f' w' ⟨interior C, isOpen_interior⟩ μ :=
    (h.mono (interior_subset.trans hWΩ)).congr_ae
      (Filter.eventually_of_mem (self_mem_ae_restrict isOpen_interior.measurableSet)
        fun z hz ↦ (Set.indicator_of_mem (interior_subset hz) f).symm)
      (Filter.eventually_of_mem (self_mem_ae_restrict isOpen_interior.measurableSet)
        fun z hz ↦ (Set.indicator_of_mem (interior_subset hz) w).symm)
  set φ : ℕ → ContDiffBump (0 : E) := fun j ↦
    ⟨ε / (2 * (j + 2)), ε / (j + 2), by positivity, by
      apply div_lt_div_of_pos_left hε (by positivity)
      nlinarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]⟩ with hφdef
  have hrOut : ∀ j, (φ j).rOut = ε / (j + 2) := fun j ↦ rfl
  have hrOutle : ∀ j, (φ j).rOut ≤ ε := fun j ↦ by
    rw [hrOut]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
  have htend : Tendsto (fun j ↦ (φ j).rOut) atTop (𝓝 0) := by
    simp only [hrOut]
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  set g : ℕ → E → F := fun j ↦ (φ j).normed μ ⋆[lsmul ℝ ℝ, μ] f' with hgdef
  have hball : ∀ j, ∀ x ∈ V, closedBall x (φ j).rOut ⊆ interior C := fun j x hx ↦
    ((closedBall_subset_closedBall (hrOutle j)).trans
      (hV'ball x (hVV' (subset_closure hx)))).trans hWC
  have hderivEq : ∀ j, ∀ x ∈ V, iteratedFDeriv ℝ n (g j) x y
      = ((φ j).normed μ ⋆[lsmul ℝ ℝ, μ] w') x := fun j x hx ↦
    hint.iteratedFDeriv_convolution (φ j).contDiff_normed
      (le_of_eq ((φ j).tsupport_normed_eq (μ := μ))) (hball j x hx)
  have hconvLp : ∀ (j : ℕ) (c : E → F), MemLp c p μ →
      MemLp ((φ j).normed μ ⋆[lsmul ℝ ℝ, μ] c) p μ := fun j _ hc ↦
    MemLp.convolution hp (memLp_one_iff_integrable.2 (φ j).integrable_normed) hc
  refine ⟨g, fun j ↦ (φ j).hasCompactSupport_normed.contDiff_convolution_left _
    (φ j).contDiff_normed hf'loc, fun j ↦ (hconvLp j f' hf'Lp).restrict V, fun j ↦ ?_, ?_, ?_⟩
  · refine ((hconvLp j w' hw'Lp).restrict V).ae_eq ?_
    filter_upwards [self_mem_ae_restrict hVo.measurableSet] with x hx
    exact (hderivEq j x hx).symm
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (ContDiffBump.tendsto_eLpNorm_convolution_sub htend hp hp' hf'Lp)
      (fun _ ↦ zero_le) (fun j ↦ ?_)
    refine le_trans (le_of_eq (eLpNorm_congr_ae ?_))
      (eLpNorm_mono_measure _ Measure.restrict_le_self)
    filter_upwards [self_mem_ae_restrict hVo.measurableSet] with x hx
    simp [hgdef, hf'def, Set.indicator_of_mem (hVC hx)]
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (ContDiffBump.tendsto_eLpNorm_convolution_sub htend hp hp' hw'Lp)
      (fun _ ↦ zero_le) (fun j ↦ ?_)
    refine le_trans (le_of_eq (eLpNorm_congr_ae ?_))
      (eLpNorm_mono_measure _ Measure.restrict_le_self)
    filter_upwards [self_mem_ae_restrict hVo.measurableSet] with x hx
    rw [hderivEq j x hx]
    simp [hw'def, Set.indicator_of_mem (hVC hx)]

end Approximation

/-! ### The product rule for two weakly differentiable factors -/

section ProductRule

open ContinuousLinearMap

variable [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] {μ : Measure E}
  [μ.IsAddHaarMeasure] {p q : ℝ≥0∞}

/-- **The product rule for weak derivatives**, with both factors merely locally integrable: if `u`
and its first-order weak derivative along `y` lie in `L^p_loc(Ω)`, and `v` and its first-order weak
derivative along `y` lie in `L^q_loc(Ω)` for the Hölder conjugate exponent `q`, then `u v` has the
weak derivative `(∂ u) v + u (∂ v)` along `y`.

This is Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional Analysis
Framework*, 3rd edition, Springer, 2009, Proposition 7.1.11, which the book states without proof.
The proof mollifies `u`, applies the case of a smooth factor
(`HasWeakIteratedLineDerivOn.mul_contDiff`) on a relatively compact open neighbourhood of the
support of the test function, and passes to the limit under Hölder's inequality. The tuple `y` is
required to have length one, as in the book, because the smooth-factor case is. -/
theorem HasWeakIteratedLineDerivOn.mul {m : ℕ} {y : Fin m → E} {u wu v wv : E → ℝ}
    (hu : HasWeakIteratedLineDerivOn y u wu Ω μ) (hm : m = 1)
    (hv : HasWeakIteratedLineDerivOn y v wv Ω μ)
    (hp : 1 ≤ p) (hp' : p ≠ ⊤) (hq' : q ≠ ⊤) [ENNReal.HolderConjugate p q]
    (hup : LocallyMemLpOn u p Ω μ) (hwup : LocallyMemLpOn wu p Ω μ)
    (hvq : LocallyMemLpOn v q Ω μ) (hwvq : LocallyMemLpOn wv q Ω μ) :
    HasWeakIteratedLineDerivOn y (fun x ↦ u x * v x) (fun x ↦ wu x * v x + u x * wv x) Ω μ := by
  subst hm
  refine ⟨hup.locallyIntegrableOn_mul hvq,
    (hwup.locallyIntegrableOn_mul hvq).add (hup.locallyIntegrableOn_mul hwvq), ?_⟩
  intro φ
  -- a relatively compact open neighbourhood `V` of the support of `φ`
  obtain ⟨V, ε, hVo, hKV, hε, hVc, hVΩ, -⟩ :=
    φ.hasCompactSupport.exists_pos_forall_closedBall_subset Ω.isOpen φ.tsupport_subset
  set Ω' : Opens E := ⟨V, hVo⟩ with hΩ'def
  have hΩ'Ω : Ω' ≤ Ω := subset_closure.trans hVΩ
  set ψ : 𝓓(Ω', ℝ) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hKV⟩ with hψdef
  have hcoe : (Ω' : Set E) = V := by rw [hΩ'def]; rfl
  have hψcoe : (ψ : E → ℝ) = (φ : E → ℝ) := by rw [hψdef]; rfl
  -- the `L^p` and `L^q` memberships on `V`
  have hres : ∀ (r : ℝ≥0∞) (c : E → ℝ), r ≠ ⊤ → LocallyMemLpOn c r Ω μ →
      MemLp c r (μ.restrict V) := fun r c hr hc ↦
    (hc.memLp_restrict_of_compact_subset hr hVΩ hVc).mono_measure
      (Measure.restrict_mono subset_closure le_rfl)
  have huν : MemLp u p (μ.restrict V) := hres p u hp' hup
  have hwuν : MemLp wu p (μ.restrict V) := hres p wu hp' hwup
  have hvν : MemLp v q (μ.restrict V) := hres q v hq' hvq
  have hwvν : MemLp wv q (μ.restrict V) := hres q wv hq' hwvq
  -- the bounded factors coming from the test function
  obtain ⟨Cφ, hCφ⟩ := φ.hasCompactSupport.exists_bound_of_continuous φ.contDiff.continuous
  obtain ⟨Cd, hCd⟩ := (φ.iteratedFDerivApply 1 y).hasCompactSupport.exists_bound_of_continuous
    (φ.iteratedFDerivApply 1 y).contDiff.continuous
  have hφtop : MemLp (φ : E → ℝ) ⊤ (μ.restrict V) :=
    memLp_top_of_bound φ.contDiff.continuous.aestronglyMeasurable Cφ (.of_forall hCφ)
  have hdtop : MemLp (fun x ↦ iteratedFDeriv ℝ 1 (φ : E → ℝ) x y) ⊤ (μ.restrict V) :=
    memLp_top_of_bound (φ.iteratedFDerivApply 1 y).contDiff.continuous.aestronglyMeasurable Cd
      (.of_forall hCd)
  have hb1 : MemLp (fun x ↦ iteratedFDeriv ℝ 1 (φ : E → ℝ) x y * v x) q (μ.restrict V) :=
    MemLp.mul' hvν hdtop
  have hb2 : MemLp (fun x ↦ (φ : E → ℝ) x * wv x) q (μ.restrict V) := MemLp.mul' hwvν hφtop
  have hb3 : MemLp (fun x ↦ (φ : E → ℝ) x * v x) q (μ.restrict V) := MemLp.mul' hvν hφtop
  -- the mollifications of `u`
  obtain ⟨g, hgsm, hgLp, hgdLp, hgt, hgdt⟩ :=
    hu.exists_seq_contDiff_tendsto_eLpNorm hup hwup hp hp' hVo hVc hVΩ
  -- the identity for each mollification, from the smooth-factor product rule
  have key : ∀ j, (∫ x in V, (iteratedFDeriv ℝ 1 (φ : E → ℝ) x y * v x) * g j x ∂μ)
      = -((∫ x in V, ((φ : E → ℝ) x * wv x) * g j x ∂μ)
        + ∫ x in V, ((φ : E → ℝ) x * v x) * iteratedFDeriv ℝ 1 (g j) x y ∂μ) := by
    intro j
    have hj := ((hv.mono hΩ'Ω).mul_contDiff rfl (hgsm j)).integral_smul_eq ψ
    rw [hcoe, hψcoe] at hj
    have i2 : Integrable (fun x ↦ ((φ : E → ℝ) x * wv x) * g j x) (μ.restrict V) :=
      memLp_one_iff_integrable.1 (MemLp.mul' (hgLp j) hb2)
    have i3 : Integrable
        (fun x ↦ ((φ : E → ℝ) x * v x) * iteratedFDeriv ℝ 1 (g j) x y) (μ.restrict V) :=
      memLp_one_iff_integrable.1 (MemLp.mul' (hgdLp j) hb3)
    have e1 : (∫ x in V, iteratedFDeriv ℝ 1 (φ : E → ℝ) x y • (v x * g j x) ∂μ)
        = ∫ x in V, (iteratedFDeriv ℝ 1 (φ : E → ℝ) x y * v x) * g j x ∂μ :=
      integral_congr_ae (Eventually.of_forall fun x ↦ by simp only [smul_eq_mul]; ring)
    have e2 : (∫ x in V, (φ : E → ℝ) x •
          (wv x * g j x + v x * iteratedFDeriv ℝ 1 (g j) x y) ∂μ)
        = (∫ x in V, ((φ : E → ℝ) x * wv x) * g j x ∂μ)
          + ∫ x in V, ((φ : E → ℝ) x * v x) * iteratedFDeriv ℝ 1 (g j) x y ∂μ := by
      rw [← integral_add i2 i3]
      exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only [smul_eq_mul]; ring)
    rw [e1, e2] at hj
    simpa using hj
  -- passing to the limit
  have hfinal : (∫ x in V, (iteratedFDeriv ℝ 1 (φ : E → ℝ) x y * v x) * u x ∂μ)
      = -((∫ x in V, ((φ : E → ℝ) x * wv x) * u x ∂μ)
        + ∫ x in V, ((φ : E → ℝ) x * v x) * wu x ∂μ) := by
    refine tendsto_nhds_unique
      (tendsto_integral_mul_of_tendsto_eLpNorm hgLp huν hb1 hgt) ?_
    simp only [key]
    exact ((tendsto_integral_mul_of_tendsto_eLpNorm hgLp huν hb2 hgt).add
      (tendsto_integral_mul_of_tendsto_eLpNorm hgdLp hwuν hb3 hgdt)).neg
  -- transporting the identity from `V` to `Ω`
  have hzeroD : ∀ x ∉ V, iteratedFDeriv ℝ 1 (φ : E → ℝ) x y = 0 := fun x hx ↦
    hψcoe ▸ (ψ.iteratedFDerivApply 1 y).eq_zero_of_notMem (by rwa [← hcoe] at hx)
  have hzeroP : ∀ x ∉ V, (φ : E → ℝ) x = 0 := fun x hx ↦
    hψcoe ▸ ψ.eq_zero_of_notMem (by rwa [← hcoe] at hx)
  have hzeroD' : ∀ x ∉ (Ω : Set E), iteratedFDeriv ℝ 1 (φ : E → ℝ) x y = 0 := fun x hx ↦
    (φ.iteratedFDerivApply 1 y).eq_zero_of_notMem hx
  have hzeroP' : ∀ x ∉ (Ω : Set E), (φ : E → ℝ) x = 0 := fun x hx ↦ φ.eq_zero_of_notMem hx
  have hL : (∫ x in (Ω : Set E), iteratedFDeriv ℝ 1 (φ : E → ℝ) x y • (u x * v x) ∂μ)
      = ∫ x in V, (iteratedFDeriv ℝ 1 (φ : E → ℝ) x y * v x) * u x ∂μ := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx ↦ by rw [hzeroD' x hx, zero_smul]),
      ← setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := V) (fun x hx ↦ by rw [hzeroD x hx, zero_smul])]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only [smul_eq_mul]; ring)
  have i4 : Integrable (fun x ↦ ((φ : E → ℝ) x * wv x) * u x) (μ.restrict V) :=
    memLp_one_iff_integrable.1 (MemLp.mul' huν hb2)
  have i5 : Integrable (fun x ↦ ((φ : E → ℝ) x * v x) * wu x) (μ.restrict V) :=
    memLp_one_iff_integrable.1 (MemLp.mul' hwuν hb3)
  have hR : (∫ x in (Ω : Set E), (φ : E → ℝ) x • (wu x * v x + u x * wv x) ∂μ)
      = (∫ x in V, ((φ : E → ℝ) x * wv x) * u x ∂μ)
        + ∫ x in V, ((φ : E → ℝ) x * v x) * wu x ∂μ := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx ↦ by rw [hzeroP' x hx, zero_smul]),
      ← setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := V) (fun x hx ↦ by rw [hzeroP x hx, zero_smul]), ← integral_add i4 i5]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only [smul_eq_mul]; ring)
  rw [hL, hR, hfinal]
  simp

end ProductRule

/-! ### The chain rule against a `C^1` function -/

section ChainRule

variable [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] {μ : Measure E}
  [μ.IsAddHaarMeasure] {p : ℝ≥0∞}

/-- A `C^1` function whose derivative is bounded by `M` is `M`-Lipschitz. -/
theorem abs_sub_le_mul_of_abs_deriv_le {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {M : ℝ}
    (hM : ∀ t, |deriv f t| ≤ M) (a b : ℝ) : |f a - f b| ≤ M * |a - b| := by
  have := (convex_univ (𝕜 := ℝ) (E := ℝ)).norm_image_sub_le_of_norm_deriv_le (f := f) (C := M)
    (fun x _ ↦ (hf.differentiable one_ne_zero).differentiableAt)
    (fun x _ ↦ by simpa [Real.norm_eq_abs] using hM x) (mem_univ b) (mem_univ a)
  simpa [Real.norm_eq_abs] using this

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- **The classical chain rule**, read on the first iterated derivative along a tuple of one
direction: `∂^y (f ∘ g) = (f' ∘ g) ∂^y g`. -/
theorem iteratedFDeriv_one_comp {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {g : E → ℝ}
    (hg : ContDiff ℝ ∞ g) (y : Fin 1 → E) (x : E) :
    iteratedFDeriv ℝ 1 (fun z ↦ f (g z)) x y = deriv f (g x) * iteratedFDeriv ℝ 1 g x y := by
  rw [iteratedFDeriv_one_apply, iteratedFDeriv_one_apply]
  have hgd : HasFDerivAt g (fderiv ℝ g x) x :=
    ((hg.differentiable (by simp)).differentiableAt).hasFDerivAt
  have hfd : HasDerivAt f (deriv f (g x)) (g x) :=
    ((hf.differentiable one_ne_zero).differentiableAt).hasDerivAt
  have hcomp : HasFDerivAt (fun z ↦ f (g z)) (deriv f (g x) • fderiv ℝ g x) x := by
    simpa [Function.comp_def] using hfd.comp_hasFDerivAt x hgd
  rw [hcomp.fderiv]
  simp

/-- **The chain rule for weak derivatives**: if `v` and its first-order weak derivative along `y`
lie in `L^p_loc(Ω)` for some `p < ∞`, and `f : ℝ → ℝ` is `C^1` with derivative bounded by `M`, then
`f ∘ v` has the weak derivative `(f' ∘ v) (∂ v)` along `y`.

This is Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional Analysis
Framework*, 3rd edition, Springer, 2009, Proposition 7.1.12, which the book states without proof
and for `v ∈ W^{1,p}` on a bounded open set; the local hypotheses here are weaker.

Unlike the product rule there is no cheap special case: `f ∘ v` cannot be integrated by parts
against a test function without first approximating `v` by smooth functions. The proof mollifies
`v` on a relatively compact open neighbourhood of the support of the test function, uses the
classical chain rule there, and passes to the limit -- in `L^1` for the terms that carry a bounded
factor, and by dominated convergence along a subsequence converging almost everywhere for the term
`(f' ∘ v_ε - f' ∘ v) ∂v`, whose convergence is not an `L^p` estimate but a pointwise one. -/
theorem HasWeakIteratedLineDerivOn.contDiff_comp {m : ℕ} {y : Fin m → E} {v w : E → ℝ}
    (h : HasWeakIteratedLineDerivOn y v w Ω μ) (hm : m = 1)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {M : ℝ} (hM : ∀ t, |deriv f t| ≤ M)
    (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    (hv : LocallyMemLpOn v p Ω μ) (hw : LocallyMemLpOn w p Ω μ) :
    HasWeakIteratedLineDerivOn y (fun x ↦ f (v x)) (fun x ↦ deriv f (v x) * w x) Ω μ := by
  subst hm
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hfc : Continuous f := hf.continuous
  have hdfc : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hlin : ∀ t, |f t| ≤ |f 0| + M * |t| := fun t ↦ by
    have h1 := abs_sub_le_mul_of_abs_deriv_le hf hM t 0
    rw [sub_zero] at h1
    have h2 : |f t| ≤ |f t - f 0| + |f 0| := by
      calc |f t| = ‖f t - f 0 + f 0‖ := by rw [Real.norm_eq_abs]; congr 1; ring
        _ ≤ ‖f t - f 0‖ + ‖f 0‖ := norm_add_le _ _
        _ = |f t - f 0| + |f 0| := by rw [Real.norm_eq_abs, Real.norm_eq_abs]
    linarith
  -- local integrability of the two functions in the statement
  have hlocf : LocallyIntegrableOn (fun x ↦ f (v x)) Ω μ := by
    intro x hx
    obtain ⟨s, hs, hvs⟩ := h.locallyIntegrableOn x hx
    refine ⟨s ∩ ball x 1, Filter.inter_mem hs (nhdsWithin_le_nhds (ball_mem_nhds x one_pos)), ?_⟩
    have hvs' : IntegrableOn v (s ∩ ball x 1) μ := hvs.mono_set Set.inter_subset_left
    have : IsFiniteMeasure (μ.restrict (s ∩ ball x 1)) := by
      constructor
      rw [Measure.restrict_apply_univ]
      exact (measure_mono Set.inter_subset_right).trans_lt measure_ball_lt_top
    have hdom : Integrable (fun z ↦ |f 0| + M * |v z|) (μ.restrict (s ∩ ball x 1)) :=
      (integrable_const (|f 0|)).add (hvs'.abs.const_mul M)
    refine Integrable.mono hdom (hfc.comp_aestronglyMeasurable hvs'.aestronglyMeasurable)
      (Eventually.of_forall fun z ↦ ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg (abs_nonneg _) (mul_nonneg hM0 (abs_nonneg _)))]
    exact hlin (v z)
  have hlocd : LocallyIntegrableOn (fun x ↦ deriv f (v x) * w x) Ω μ := by
    intro x hx
    obtain ⟨s, hs, hvs⟩ := h.locallyIntegrableOn x hx
    obtain ⟨t, ht, hws⟩ := h.locallyIntegrableOn_weakDeriv x hx
    refine ⟨s ∩ t, Filter.inter_mem hs ht, ?_⟩
    have hvs' : IntegrableOn v (s ∩ t) μ := hvs.mono_set Set.inter_subset_left
    have hws' : IntegrableOn w (s ∩ t) μ := hws.mono_set Set.inter_subset_right
    refine Integrable.mono (hws'.abs.const_mul M) ?_ (Eventually.of_forall fun z ↦ ?_)
    · exact (hdfc.comp_aestronglyMeasurable hvs'.aestronglyMeasurable).mul
        hws'.aestronglyMeasurable
    · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (mul_nonneg hM0 (abs_nonneg (w z)))]
      exact mul_le_mul_of_nonneg_right (hM _) (abs_nonneg _)
  refine ⟨hlocf, hlocd, ?_⟩
  intro φ
  -- a relatively compact open neighbourhood `V` of the support of `φ`
  obtain ⟨V, ε, hVo, hKV, hε, hVc, hVΩ, -⟩ :=
    φ.hasCompactSupport.exists_pos_forall_closedBall_subset Ω.isOpen φ.tsupport_subset
  set Ω' : Opens E := ⟨V, hVo⟩ with hΩ'def
  have hΩ'Ω : Ω' ≤ Ω := subset_closure.trans hVΩ
  set ψ : 𝓓(Ω', ℝ) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hKV⟩ with hψdef
  have hcoe : (Ω' : Set E) = V := by rw [hΩ'def]; rfl
  have hψcoe : (ψ : E → ℝ) = (φ : E → ℝ) := by rw [hψdef]; rfl
  have hνfin : IsFiniteMeasure (μ.restrict V) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_lt (measure_mono subset_closure) hVc.measure_lt_top
  have hvν : MemLp v p (μ.restrict V) :=
    (hv.memLp_restrict_of_compact_subset hp' hVΩ hVc).mono_measure
      (Measure.restrict_mono subset_closure le_rfl)
  have hwν : MemLp w p (μ.restrict V) :=
    (hw.memLp_restrict_of_compact_subset hp' hVΩ hVc).mono_measure
      (Measure.restrict_mono subset_closure le_rfl)
  -- the mollifications of `v`, along a subsequence converging almost everywhere
  obtain ⟨g₀, hg₀sm, hg₀Lp, hg₀dLp, hg₀t, hg₀dt⟩ :=
    h.exists_seq_contDiff_tendsto_eLpNorm hv hw hp hp' hVo hVc hVΩ
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (p := p) (μ := μ.restrict V)
      (lt_of_lt_of_le zero_lt_one hp).ne' (fun j ↦ (hg₀Lp j).1) hvν.1 hg₀t).exists_seq_tendsto_ae
  set g : ℕ → E → ℝ := fun k ↦ g₀ (ns k) with hgdef
  have hgsm : ∀ k, ContDiff ℝ ∞ (g k) := fun k ↦ hg₀sm (ns k)
  have hgLp : ∀ k, MemLp (g k) p (μ.restrict V) := fun k ↦ hg₀Lp (ns k)
  have hgdLp : ∀ k, MemLp (fun x ↦ iteratedFDeriv ℝ 1 (g k) x y) p (μ.restrict V) := fun k ↦
    hg₀dLp (ns k)
  have hgt : Tendsto (fun k ↦ eLpNorm (fun x ↦ g k x - v x) p (μ.restrict V)) atTop (𝓝 0) :=
    hg₀t.comp hns.tendsto_atTop
  have hgdt : Tendsto
      (fun k ↦ eLpNorm (fun x ↦ iteratedFDeriv ℝ 1 (g k) x y - w x) p (μ.restrict V))
      atTop (𝓝 0) := hg₀dt.comp hns.tendsto_atTop
  -- everything relevant is integrable on `V`, the measure being finite
  have hvL1 : MemLp v 1 (μ.restrict V) := hvν.mono_exponent hp
  have hwL1 : MemLp w 1 (μ.restrict V) := hwν.mono_exponent hp
  have hgL1 : ∀ k, MemLp (g k) 1 (μ.restrict V) := fun k ↦ (hgLp k).mono_exponent hp
  have hgdL1 : ∀ k, MemLp (fun x ↦ iteratedFDeriv ℝ 1 (g k) x y) 1 (μ.restrict V) := fun k ↦
    (hgdLp k).mono_exponent hp
  have hgt1 : Tendsto (fun k ↦ eLpNorm (fun x ↦ g k x - v x) 1 (μ.restrict V)) atTop (𝓝 0) :=
    tendsto_eLpNorm_one_of_tendsto_eLpNorm hp (fun k ↦ ((hgLp k).sub hvν).1) hgt
  have hgdt1 : Tendsto
      (fun k ↦ eLpNorm (fun x ↦ iteratedFDeriv ℝ 1 (g k) x y - w x) 1 (μ.restrict V))
      atTop (𝓝 0) := tendsto_eLpNorm_one_of_tendsto_eLpNorm hp (fun k ↦ ((hgdLp k).sub hwν).1) hgdt
  -- `f` composed with an `L^1` function is `L^1`
  have hcompL1 : ∀ c : E → ℝ, MemLp c 1 (μ.restrict V) →
      MemLp (fun x ↦ f (c x)) 1 (μ.restrict V) := by
    intro c hc
    have hdom : MemLp (fun x ↦ |f 0| + M * |c x|) 1 (μ.restrict V) :=
      (memLp_const (|f 0|)).add (hc.abs.const_mul M)
    refine MemLp.of_le hdom (hfc.comp_aestronglyMeasurable hc.1)
      (Eventually.of_forall fun z ↦ ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg (abs_nonneg _) (mul_nonneg hM0 (abs_nonneg _)))]
    exact hlin (c z)
  -- the bounded factors coming from the test function
  obtain ⟨Cφ, hCφ⟩ := φ.hasCompactSupport.exists_bound_of_continuous φ.contDiff.continuous
  obtain ⟨Cd, hCd⟩ := (φ.iteratedFDerivApply 1 y).hasCompactSupport.exists_bound_of_continuous
    (φ.iteratedFDerivApply 1 y).contDiff.continuous
  have hCφ' : ∀ z, |(φ : E → ℝ) z| ≤ Cφ := fun z ↦ by simpa [Real.norm_eq_abs] using hCφ z
  have hCφ0 : 0 ≤ Cφ := le_trans (abs_nonneg _) (hCφ' 0)
  have hdtop : MemLp (fun x ↦ iteratedFDeriv ℝ 1 (φ : E → ℝ) x y) ⊤ (μ.restrict V) :=
    memLp_top_of_bound (φ.iteratedFDerivApply 1 y).contDiff.continuous.aestronglyMeasurable Cd
      (.of_forall hCd)
  -- a bounded factor times an `L^1` function is `L^1`
  have hbdmul : ∀ (b d : E → ℝ) (C : ℝ), 0 ≤ C → (∀ z, |b z| ≤ C) →
      AEStronglyMeasurable b (μ.restrict V) → MemLp d 1 (μ.restrict V) →
      MemLp (fun x ↦ b x * d x) 1 (μ.restrict V) := by
    intro b d C hC0 hCb hbm hd
    have hdom : MemLp (fun x ↦ C * |d x|) 1 (μ.restrict V) := hd.abs.const_mul C
    refine MemLp.of_le hdom (hbm.mul hd.1) (Eventually.of_forall fun z ↦ ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg hC0 (abs_nonneg _))]
    exact mul_le_mul_of_nonneg_right (hCb z) (abs_nonneg _)
  have hφdm : ∀ c : E → ℝ, AEStronglyMeasurable c (μ.restrict V) →
      AEStronglyMeasurable (fun x ↦ (φ : E → ℝ) x * deriv f (c x)) (μ.restrict V) := fun c hc ↦
    φ.contDiff.continuous.aestronglyMeasurable.mul (hdfc.comp_aestronglyMeasurable hc)
  have hφdb : ∀ c : E → ℝ, ∀ z, |(φ : E → ℝ) z * deriv f (c z)| ≤ Cφ * M := fun c z ↦ by
    rw [abs_mul]
    exact mul_le_mul (hCφ' z) (hM _) (abs_nonneg _) hCφ0
  have hIinf : MemLp (fun x ↦ ((φ : E → ℝ) x * deriv f (v x)) * w x) 1 (μ.restrict V) :=
    hbdmul _ _ (Cφ * M) (mul_nonneg hCφ0 hM0) (hφdb v) (hφdm v hvL1.1) hwL1
  have hIk : ∀ k, MemLp (fun x ↦ ((φ : E → ℝ) x * deriv f (g k x)) *
      iteratedFDeriv ℝ 1 (g k) x y) 1 (μ.restrict V) := fun k ↦
    hbdmul _ _ (Cφ * M) (mul_nonneg hCφ0 hM0) (hφdb (g k)) (hφdm (g k) (hgL1 k).1) (hgdL1 k)
  -- the identity for each mollification, from the classical chain rule
  have key : ∀ k, (∫ x in V, iteratedFDeriv ℝ 1 (φ : E → ℝ) x y * f (g k x) ∂μ)
      = -∫ x in V, ((φ : E → ℝ) x * deriv f (g k x)) * iteratedFDeriv ℝ 1 (g k) x y ∂μ := by
    intro k
    have hcd : ContDiff ℝ 1 (fun z ↦ f (g k z)) := hf.comp ((hgsm k).of_le (by simp))
    have h1 := (hcd.contDiffOn (s := (Ω' : Set E))).hasWeakIteratedFDerivOn (μ := μ) (m := 1)
      le_rfl
    have h2 := h1.lineDeriv y
    rw [funext (fun x ↦ iteratedFDeriv_one_comp hf (hgsm k) y x)] at h2
    have hj := h2.integral_smul_eq ψ
    rw [hcoe, hψcoe] at hj
    simpa [smul_eq_mul, mul_assoc] using hj
  -- limit of the left-hand sides
  have hfgt : Tendsto (fun k ↦ eLpNorm (fun x ↦ f (g k x) - f (v x)) 1 (μ.restrict V))
      atTop (𝓝 0) := by
    have hbd : ∀ k, eLpNorm (fun x ↦ f (g k x) - f (v x)) 1 (μ.restrict V)
        ≤ ‖M‖ₑ * eLpNorm (fun x ↦ g k x - v x) 1 (μ.restrict V) := by
      intro k
      rw [← eLpNorm_const_smul M (fun x ↦ g k x - v x) 1 (μ.restrict V)]
      refine eLpNorm_mono fun x ↦ ?_
      rw [Real.norm_eq_abs, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg hM0]
      exact abs_sub_le_mul_of_abs_deriv_le hf hM _ _
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ ↦ zero_le) hbd
    simpa using ENNReal.Tendsto.const_mul hgt1 (Or.inr (by simp))
  have hLHS : Tendsto (fun k ↦ ∫ x in V, iteratedFDeriv ℝ 1 (φ : E → ℝ) x y * f (g k x) ∂μ)
      atTop (𝓝 (∫ x in V, iteratedFDeriv ℝ 1 (φ : E → ℝ) x y * f (v x) ∂μ)) :=
    tendsto_integral_mul_of_tendsto_eLpNorm (fun k ↦ hcompL1 _ (hgL1 k)) (hcompL1 _ hvL1) hdtop
      hfgt
  -- limit of the right-hand sides, in two steps
  have hT1 : Tendsto (fun k ↦ ∫ x in V,
      ((φ : E → ℝ) x * deriv f (g k x)) * (iteratedFDeriv ℝ 1 (g k) x y - w x) ∂μ)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hbd : ∀ k, ‖∫ x in V,
        ((φ : E → ℝ) x * deriv f (g k x)) * (iteratedFDeriv ℝ 1 (g k) x y - w x) ∂μ‖
        ≤ (ENNReal.ofReal (Cφ * M) *
          eLpNorm (fun x ↦ iteratedFDeriv ℝ 1 (g k) x y - w x) 1 (μ.restrict V)).toReal := by
      intro k
      have hfin : ENNReal.ofReal (Cφ * M) *
          eLpNorm (fun x ↦ iteratedFDeriv ℝ 1 (g k) x y - w x) 1 (μ.restrict V) ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top ((hgdL1 k).sub hwL1).2.ne
      calc ‖∫ x in V, ((φ : E → ℝ) x * deriv f (g k x)) *
              (iteratedFDeriv ℝ 1 (g k) x y - w x) ∂μ‖
          = ‖∫ x in V, ((φ : E → ℝ) x * deriv f (g k x)) *
              (iteratedFDeriv ℝ 1 (g k) x y - w x) ∂μ‖ₑ.toReal := by
            rw [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _)]
        _ ≤ _ := ENNReal.toReal_mono hfin (enorm_integral_smul_le_of_bound (hφdb (g k)))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun _ ↦ norm_nonneg _) hbd
    rw [show (0 : ℝ) = (0 : ℝ≥0∞).toReal by simp]
    refine (ENNReal.tendsto_toReal (by simp)).comp ?_
    simpa using ENNReal.Tendsto.const_mul hgdt1 (Or.inr ENNReal.ofReal_ne_top)
  have hT2 : Tendsto (fun k ↦ ∫ x in V,
      ((φ : E → ℝ) x * (deriv f (g k x) - deriv f (v x))) * w x ∂μ) atTop (𝓝 0) := by
    have hzero : (0 : ℝ) = ∫ _x in V, (0 : ℝ) ∂μ := by simp
    rw [hzero]
    refine tendsto_integral_of_dominated_convergence (fun x ↦ (Cφ * (2 * M)) * |w x|)
      (fun k ↦ ?_) (memLp_one_iff_integrable.1 (hwL1.abs.const_mul (Cφ * (2 * M))))
      (fun k ↦ Eventually.of_forall fun z ↦ ?_) ?_
    · exact (φ.contDiff.continuous.aestronglyMeasurable.mul
        ((hdfc.comp_aestronglyMeasurable (hgL1 k).1).sub
          (hdfc.comp_aestronglyMeasurable hvL1.1))).mul hwL1.1
    · have h2 : |deriv f (g k z) - deriv f (v z)| ≤ 2 * M := by
        have := abs_sub (deriv f (g k z)) (deriv f (v z))
        linarith [hM (g k z), hM (v z), abs_sub_abs_le_abs_sub (deriv f (g k z)) (deriv f (v z))]
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (hCφ' z) h2 (abs_nonneg _) hCφ0) (abs_nonneg _)
    · filter_upwards [hae] with z hz
      have hd : Tendsto (fun k ↦ deriv f (g k z)) atTop (𝓝 (deriv f (v z))) :=
        (hdfc.tendsto (v z)).comp hz
      have : Tendsto (fun k ↦ ((φ : E → ℝ) z * (deriv f (g k z) - deriv f (v z))) * w z) atTop
          (𝓝 (((φ : E → ℝ) z * (deriv f (v z) - deriv f (v z))) * w z)) :=
        ((tendsto_const_nhds.mul (hd.sub tendsto_const_nhds)).mul tendsto_const_nhds)
      simpa using this
  have hRHS : Tendsto (fun k ↦ ∫ x in V,
      ((φ : E → ℝ) x * deriv f (g k x)) * iteratedFDeriv ℝ 1 (g k) x y ∂μ)
      atTop (𝓝 (∫ x in V, ((φ : E → ℝ) x * deriv f (v x)) * w x ∂μ)) := by
    have hsplit : ∀ k, (∫ x in V, ((φ : E → ℝ) x * deriv f (g k x)) *
          iteratedFDeriv ℝ 1 (g k) x y ∂μ)
        = (∫ x in V, ((φ : E → ℝ) x * deriv f (g k x)) *
            (iteratedFDeriv ℝ 1 (g k) x y - w x) ∂μ)
          + (∫ x in V, ((φ : E → ℝ) x * (deriv f (g k x) - deriv f (v x))) * w x ∂μ)
          + ∫ x in V, ((φ : E → ℝ) x * deriv f (v x)) * w x ∂μ := by
      intro k
      have i1 : Integrable (fun x ↦ ((φ : E → ℝ) x * deriv f (g k x)) *
          (iteratedFDeriv ℝ 1 (g k) x y - w x)) (μ.restrict V) :=
        memLp_one_iff_integrable.1 (hbdmul _ _ (Cφ * M) (mul_nonneg hCφ0 hM0) (hφdb (g k))
          (hφdm (g k) (hgL1 k).1) ((hgdL1 k).sub hwL1))
      have i2 : Integrable (fun x ↦ ((φ : E → ℝ) x * (deriv f (g k x) - deriv f (v x))) * w x)
          (μ.restrict V) := by
        refine memLp_one_iff_integrable.1 (hbdmul _ _ (Cφ * (2 * M))
          (by positivity) (fun z ↦ ?_) ?_ hwL1)
        · rw [abs_mul]
          refine mul_le_mul (hCφ' z) ?_ (abs_nonneg _) hCφ0
          have h3 : |deriv f (g k z) - deriv f (v z)| ≤ |deriv f (g k z)| + |deriv f (v z)| := by
            simpa [Real.norm_eq_abs] using norm_sub_le (deriv f (g k z)) (deriv f (v z))
          linarith [hM (g k z), hM (v z)]
        · exact φ.contDiff.continuous.aestronglyMeasurable.mul
            ((hdfc.comp_aestronglyMeasurable (hgL1 k).1).sub
              (hdfc.comp_aestronglyMeasurable hvL1.1))
      have i12 : Integrable (fun x ↦ ((φ : E → ℝ) x * deriv f (g k x)) *
          (iteratedFDeriv ℝ 1 (g k) x y - w x)
          + ((φ : E → ℝ) x * (deriv f (g k x) - deriv f (v x))) * w x) (μ.restrict V) := i1.add i2
      rw [← integral_add i1 i2, ← integral_add i12 (memLp_one_iff_integrable.1 hIinf)]
      exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
    simp only [hsplit]
    simpa using (hT1.add hT2).add
      (tendsto_const_nhds (x := ∫ x in V, ((φ : E → ℝ) x * deriv f (v x)) * w x ∂μ))
  -- the identity in the limit, transported from `V` to `Ω`
  have hfinal : (∫ x in V, iteratedFDeriv ℝ 1 (φ : E → ℝ) x y * f (v x) ∂μ)
      = -∫ x in V, ((φ : E → ℝ) x * deriv f (v x)) * w x ∂μ := by
    refine tendsto_nhds_unique hLHS ?_
    simp only [key]
    exact hRHS.neg
  have hzeroD : ∀ x ∉ V, iteratedFDeriv ℝ 1 (φ : E → ℝ) x y = 0 := fun x hx ↦
    hψcoe ▸ (ψ.iteratedFDerivApply 1 y).eq_zero_of_notMem (by rwa [← hcoe] at hx)
  have hzeroP : ∀ x ∉ V, (φ : E → ℝ) x = 0 := fun x hx ↦
    hψcoe ▸ ψ.eq_zero_of_notMem (by rwa [← hcoe] at hx)
  have hzeroD' : ∀ x ∉ (Ω : Set E), iteratedFDeriv ℝ 1 (φ : E → ℝ) x y = 0 := fun x hx ↦
    (φ.iteratedFDerivApply 1 y).eq_zero_of_notMem hx
  have hzeroP' : ∀ x ∉ (Ω : Set E), (φ : E → ℝ) x = 0 := fun x hx ↦ φ.eq_zero_of_notMem hx
  have hL : (∫ x in (Ω : Set E), iteratedFDeriv ℝ 1 (φ : E → ℝ) x y • f (v x) ∂μ)
      = ∫ x in V, iteratedFDeriv ℝ 1 (φ : E → ℝ) x y * f (v x) ∂μ := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx ↦ by rw [hzeroD' x hx, zero_smul]),
      ← setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := V) (fun x hx ↦ by rw [hzeroD x hx, zero_smul])]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only [smul_eq_mul])
  have hR : (∫ x in (Ω : Set E), (φ : E → ℝ) x • (deriv f (v x) * w x) ∂μ)
      = ∫ x in V, ((φ : E → ℝ) x * deriv f (v x)) * w x ∂μ := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx ↦ by rw [hzeroP' x hx, zero_smul]),
      ← setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := V) (fun x hx ↦ by rw [hzeroP x hx, zero_smul])]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only [smul_eq_mul, mul_assoc])
  rw [hL, hR, hfinal]
  simp

end ChainRule
