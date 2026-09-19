import Mathlib.Analysis.Normed.Affine.Convex
import Numlib.Analysis.Sobolev.Calculus
import Numlib.Analysis.Sobolev.Friedrichs
import NumlibSurface.Brezis.Chapter03.Section05
import NumlibSurface.Brezis.Chapter03.Section06
import NumlibSurface.Brezis.Chapter04.Section03
import NumlibSurface.Brezis.Chapter04.Section04

/-!
# Brezis §9.1: definition and elementary properties of the Sobolev spaces `W^{1,p}(Ω)`

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §9.1, together with the paragraph "The spaces
`W^{m,p}(Ω)`" that closes the section, on an open set `Ω ⊆ ℝ^N = EuclideanSpace ℝ (Fin N)` with
Lebesgue measure.

The book's `W^{1,p}(Ω)` is `sobolevSpace N p Ω := SobolevEuclidean N 1 p Ω`
(`Numlib/Analysis/Sobolev/MultiIndex`): the multi-index Sobolev space over the standard basis of
`ℝ^N`, an `abbrev` so that every backbone lemma applies. Its elements carry a function
`SobolevMultiIndex.fn u`, defined up to a null set of `Ω`, and the weak partial derivatives
`partialDeriv u i = ∂u/∂x_i ∈ L^p(Ω)`; `sobolevSpace_iff` is the book's displayed definition. The
norm of the type is the book's "sometimes equivalent norm" `(‖u‖_p^p + ∑ ‖∂_i u‖_p^p)^{1/p}`; the
norm the book equips `W^{1,p}(Ω)` with, `‖u‖_p + ∑ ‖∂_i u‖_p`, is `bookNorm`, equivalent to it by
`bookNorm_equiv`. At `p = 2` the type's norm *is* the book's `H^1` norm and its inner product the
book's `(u, v)_{H^1}` (`hInner`, `hNorm`). The gradient `∇u = (∂_1 u, …, ∂_N u)` is the vector
field `gradient u`, and `‖∇u‖_{L^p(Ω)}` is `eLpNorm (gradient u) p (volume.restrict Ω)`.

The backbone theorems are stated over a general finite-dimensional space with a Haar measure in the
`HasWeakFDerivOn` / `MemSobolev` / `MemSobolevMultiIndex` readings; the surface instantiates them on
`ℝ^N` and converts between the tensor gradient and the partial derivatives
(`exists_hasWeakFDerivOn_fn_gradient`). Test functions are `𝓓(Ω, ℝ) = C_c^∞(Ω)`; Remark 1, that
`C_c^1(Ω)` may be used instead, is `remark_9_1` and `remark_9_1_iff`.

## Main results

* `sobolevSpace`, `sobolevSpace_iff`, `partialDeriv`, `partialDeriv_spec`, `gradient` — the
  Definition; `remark_9_1`, `remark_9_1_iff` — `C_c^1` test functions; `hSpace`, `hInner`,
  `hNorm` — `H^1(Ω)`; `bookNorm`, `bookNorm_equiv` — the norm.
* `proposition_9_1` — `W^{1,p}(Ω)` is a Banach space, reflexive for `1 < p < ∞`, separable for
  `p < ∞`; `H^1(Ω)` is a separable Hilbert space.
* `remark_9_2`, `remark_9_2_closure`, `remark_9_2_converse` — `C^1` functions in `W^{1,p}`, and
  the `C^1` representative of a function with continuous weak derivatives.
* `remark_9_4_i`, `remark_9_4_i_bounded`, `remark_9_4_ii`, `remark_9_4_ii_cutoff` — closedness
  under `L^p` limits, and the extension by zero of `α u`.
* `IsStronglyIncluded`, `theorem_9_2`, `theorem_9_2_univ`, `lemma_9_1`, `remark_9_5` — Friedrichs'
  theorem, convolution with an `L^1` kernel, Meyers–Serrin.
* `proposition_9_3` (the `TFAE`), `proposition_9_3_i_ii`, `proposition_9_3_ii_i`,
  `proposition_9_3_i_iii`, `proposition_9_3_iii_ii`, `proposition_9_3_univ`, `remark_9_6` — the
  characterizations of `W^{1,p}`, with the book's `dist(ω, ∂Ω)` as `edistFrontier`;
  `remark_9_7`, `remark_9_7_convex`, `remark_9_7_const` — `W^{1,∞}` and Lipschitz functions.
* `proposition_9_4`, `proposition_9_5`, `proposition_9_6` — products, compositions, change of
  variables.
* `sobolevSpaceHigher`, `sobolevSpaceHigher_iff`, `sobolevSpaceHigher_iff_inductive`,
  `sobolevSpaceHigher_banach`, `hSpaceHigher` — the spaces `W^{m,p}(Ω)` and `H^m(Ω)`.
-/

open Filter MeasureTheory Metric Topology TopologicalSpace
open scoped ContDiff Convolution Distributions ENNReal

namespace Brezis.Chapter09

variable {N : ℕ}

/-- The book's `ℝ^N`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

/-- The standard basis of `ℝ^N`, as a `Basis`. -/
local notation "𝔟" => OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin N) ℝ)

/-! ### Weak derivatives along one direction, in the book's form -/

section Direction

variable {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- The defining identity of a weak derivative along a tuple `y` of `n` directions, in the
book's form: `∫_Ω u D^y φ = (−1)^n ∫_Ω g φ`. -/
theorem integral_mul_iteratedFDeriv_eq_of_hasWeakIteratedLineDerivOn {u g : 𝔼 → ℝ} {n : ℕ}
    {y : Fin n → 𝔼} (h : HasWeakIteratedLineDerivOn y u g Ω volume) (φ : 𝓓(Ω, ℝ)) :
    ∫ x in (Ω : Set 𝔼), u x * iteratedFDeriv ℝ n φ x y
      = (-1) ^ n * ∫ x in (Ω : Set 𝔼), g x * φ x := by
  have hs := Ω.isOpen.measurableSet
  have h1 := h.integral_smul_eq φ
  simp only [smul_eq_mul] at h1
  calc ∫ x in (Ω : Set 𝔼), u x * iteratedFDeriv ℝ n φ x y
      = ∫ x in (Ω : Set 𝔼), iteratedFDeriv ℝ n φ x y * u x :=
        setIntegral_congr_fun hs fun x _ ↦ mul_comm _ _
    _ = (-1) ^ n * ∫ x in (Ω : Set 𝔼), φ x * g x := h1
    _ = (-1) ^ n * ∫ x in (Ω : Set 𝔼), g x * φ x := by
        rw [setIntegral_congr_fun hs fun x _ ↦ mul_comm (φ x) (g x)]

/-- A weak derivative along a tuple `y` of `n` directions, from the book's identity
`∫_Ω u D^y φ = (−1)^n ∫_Ω g φ` and local integrability. -/
theorem hasWeakIteratedLineDerivOn_of_forall {u g : 𝔼 → ℝ} {n : ℕ} {y : Fin n → 𝔼}
    (hu : LocallyIntegrableOn u Ω volume) (hg : LocallyIntegrableOn g Ω volume)
    (h : ∀ φ : 𝓓(Ω, ℝ), ∫ x in (Ω : Set 𝔼), u x * iteratedFDeriv ℝ n φ x y
      = (-1) ^ n * ∫ x in (Ω : Set 𝔼), g x * φ x) :
    HasWeakIteratedLineDerivOn y u g Ω volume := by
  have hs := Ω.isOpen.measurableSet
  refine ⟨hu, hg, fun φ ↦ ?_⟩
  simp only [smul_eq_mul]
  calc ∫ x in (Ω : Set 𝔼), iteratedFDeriv ℝ n φ x y * u x
      = ∫ x in (Ω : Set 𝔼), u x * iteratedFDeriv ℝ n φ x y :=
        setIntegral_congr_fun hs fun x _ ↦ mul_comm _ _
    _ = (-1) ^ n * ∫ x in (Ω : Set 𝔼), g x * φ x := h φ
    _ = (-1) ^ n * ∫ x in (Ω : Set 𝔼), φ x * g x := by
        rw [setIntegral_congr_fun hs fun x _ ↦ mul_comm (g x) (φ x)]

/-- The defining identity of a weak derivative along a single direction `y`, in the book's
form: `∫_Ω u ∂_y φ = −∫_Ω g φ`. -/
theorem integral_mul_fderiv_eq_of_hasWeakIteratedLineDerivOn {u g : 𝔼 → ℝ} {y : 𝔼}
    (h : HasWeakIteratedLineDerivOn ![y] u g Ω volume) (φ : 𝓓(Ω, ℝ)) :
    ∫ x in (Ω : Set 𝔼), u x * fderiv ℝ φ x y = -∫ x in (Ω : Set 𝔼), g x * φ x := by
  have := integral_mul_iteratedFDeriv_eq_of_hasWeakIteratedLineDerivOn h φ
  simpa [iteratedFDeriv_one_apply] using this

/-- A weak derivative along a single direction `y`, from the book's identity
`∫_Ω u ∂_y φ = −∫_Ω g φ` and local integrability. -/
theorem hasWeakIteratedLineDerivOn_single_of_forall {u g : 𝔼 → ℝ} {y : 𝔼}
    (hu : LocallyIntegrableOn u Ω volume) (hg : LocallyIntegrableOn g Ω volume)
    (h : ∀ φ : 𝓓(Ω, ℝ), ∫ x in (Ω : Set 𝔼), u x * fderiv ℝ φ x y = -∫ x in (Ω : Set 𝔼), g x * φ x) :
    HasWeakIteratedLineDerivOn ![y] u g Ω volume :=
  hasWeakIteratedLineDerivOn_of_forall hu hg fun φ ↦ by
    simpa [iteratedFDeriv_one_apply] using h φ

end Direction

/-! ### The Definition -/

/-- **The Sobolev space `W^{1,p}(Ω)`** of §9.1: the functions `u ∈ L^p(Ω)` with weak partial
derivatives `∂u/∂x_i ∈ L^p(Ω)` (`sobolevSpace_iff` for the displayed definition), as the backbone
type `SobolevEuclidean N 1 p Ω`. The norm of the type is the book's second, equivalent norm
`(‖u‖_p^p + ∑ ‖∂_i u‖_p^p)^{1/p}` (`SobolevMultiIndex.norm_eq_sum`); the book's first norm is
`bookNorm`. -/
noncomputable abbrev sobolevSpace (N : ℕ) (p : ℝ≥0∞) (Ω : Opens (EuclideanSpace ℝ (Fin N))) :
    Type :=
  SobolevEuclidean N 1 p Ω

variable {p : ℝ≥0∞} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **The weak partial derivative `∂u/∂x_i`** of `u ∈ W^{1,p}(Ω)`, the function `g_i` of the
Definition, as an element of `L^p(Ω)`. -/
noncomputable def partialDeriv (u : sobolevSpace N p Ω) (i : Fin N) :
    Lp ℝ p (volume.restrict (Ω : Set 𝔼)) :=
  SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i)

/-- **The gradient `∇u = (∂u/∂x_1, …, ∂u/∂x_N)`** of `u ∈ W^{1,p}(Ω)`, as an `ℝ^N`-valued
function on `ℝ^N` (defined up to a null set of `Ω`); `‖∇u‖_{L^p(Ω)}` is
`eLpNorm (gradient u) p (volume.restrict Ω)`. -/
noncomputable def gradient (u : sobolevSpace N p Ω) (x : 𝔼) : 𝔼 :=
  WithLp.toLp 2 fun i ↦ partialDeriv u i x

/-- The `i`-th component of the gradient is `∂u/∂x_i`. -/
@[simp]
theorem gradient_apply (u : sobolevSpace N p Ω) (x : 𝔼) (i : Fin N) :
    gradient u x i = partialDeriv u i x :=
  rfl

/-- The standard basis vector `e_i` of `ℝ^N` is `EuclideanSpace.single i 1`. -/
theorem basisFun_toBasis_apply (i : Fin N) :
    (𝔟 : Fin N → 𝔼) i = EuclideanSpace.single i 1 := by
  simp

/-- The weak partial derivative `∂u/∂x_i` is the weak derivative of `u` along `e_i` on `Ω`, in
the backbone's sense. -/
theorem hasWeakIteratedLineDerivOn_partialDeriv (u : sobolevSpace N p Ω) (i : Fin N) :
    HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1] (SobolevMultiIndex.fn u)
      (partialDeriv u i) Ω volume := by
  have := (SobolevMultiIndex.hasWeakIteratedLineDerivOn u (MultiIndexLE.single i)).of_perm
    (multiIndexTuple_single_perm (𝔟 : Fin N → 𝔼) i)
  rw [basisFun_toBasis_apply] at this
  exact this

/-- **The defining identity of `∂u/∂x_i`**: `∫_Ω u ∂φ/∂x_i = −∫_Ω (∂u/∂x_i) φ` for every test
function `φ ∈ C_c^∞(Ω)`. -/
theorem partialDeriv_spec (u : sobolevSpace N p Ω) (i : Fin N) (φ : 𝓓(Ω, ℝ)) :
    ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn u x * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = -∫ x in (Ω : Set 𝔼), partialDeriv u i x * φ x :=
  integral_mul_fderiv_eq_of_hasWeakIteratedLineDerivOn
    (hasWeakIteratedLineDerivOn_partialDeriv u i) φ

variable [Fact (1 ≤ p)]

/-- A function of `L^p(Ω)` whose weak partial derivatives along the `e_i` lie in `L^p(Ω)` is, up
to a null set of `Ω`, the function of an element of `W^{1,p}(Ω)`, whose partial derivatives are
the given ones. -/
theorem exists_sobolevSpace_of_hasWeakIteratedLineDerivOn {u : 𝔼 → ℝ}
    (hu : MemLp u p (volume.restrict (Ω : Set 𝔼))) {g : Fin N → 𝔼 → ℝ}
    (hg : ∀ i, HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1] u (g i) Ω volume)
    (hgp : ∀ i, MemLp (g i) p (volume.restrict (Ω : Set 𝔼))) :
    ∃ v : sobolevSpace N p Ω, SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼)] u ∧
      ∀ i, partialDeriv v i =ᵐ[volume.restrict (Ω : Set 𝔼)] g i := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hmem : MemSobolevMultiIndex 𝔟 u 1 p Ω volume := by
    refine ⟨hu, fun α hα ↦ ?_⟩
    rcases MultiIndexLE.eq_zero_or_exists_eq_single (⟨α, hα⟩ : MultiIndexLE (Fin N) 1) with
      h0 | ⟨i, hi⟩
    · obtain rfl : α = 0 := congrArg Subtype.val h0
      exact ⟨u, HasWeakIteratedLineDerivOn.of_length_eq_zero (by simp) _
        (hu.locallyIntegrableOn hp), hu⟩
    · obtain rfl : α = Pi.single i 1 := congrArg Subtype.val hi
      have hperm := (multiIndexTuple_single_perm (𝔟 : Fin N → 𝔼) i).symm
      rw [basisFun_toBasis_apply] at hperm
      exact ⟨g i, (hg i).of_perm hperm, hgp i⟩
  obtain ⟨v, hv⟩ := hmem.exists_sobolevMultiIndex
  refine ⟨v, hv, fun i ↦ ?_⟩
  have h1 := (hasWeakIteratedLineDerivOn_partialDeriv v i).congr_ae hv
    (Filter.EventuallyEq.refl _ _)
  exact (ae_restrict_iff' Ω.isOpen.measurableSet).2 (h1.ae_eq (hg i))

omit [Fact (1 ≤ p)] in
/-- The weak derivative along `e_i` of a function of `W^{1,p}(Ω)` (in the predicate sense) lies
in `L^p(Ω)`: `L^p` membership transfers along the almost everywhere uniqueness of weak
derivatives. -/
theorem memLp_of_memSobolevMultiIndex_of_hasWeakIteratedLineDerivOn {u g : 𝔼 → ℝ}
    (hu : MemSobolevMultiIndex 𝔟 u 1 p Ω volume) {i : Fin N}
    (hg : HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1] u g Ω volume) :
    MemLp g p (volume.restrict (Ω : Set 𝔼)) := by
  obtain ⟨w, hw, hwp⟩ := hu.2 (Pi.single i 1) (by simp)
  have hperm := multiIndexTuple_single_perm (𝔟 : Fin N → 𝔼) i
  rw [basisFun_toBasis_apply] at hperm
  exact hwp.ae_eq ((ae_restrict_iff' Ω.isOpen.measurableSet).2 ((hw.of_perm hperm).ae_eq hg))

/-- **The Definition of `W^{1,p}(Ω)`**: a function `u : ℝ^N → ℝ` is (almost everywhere on `Ω`)
the function of an element of `W^{1,p}(Ω)` if and only if `u ∈ L^p(Ω)` and there are
`g_1, …, g_N ∈ L^p(Ω)` with `∫_Ω u ∂φ/∂x_i = −∫_Ω g_i φ` for every `φ ∈ C_c^∞(Ω)` and every `i`.
(Footnote 2, that the `g_i` are unique almost everywhere, is `partialDeriv_spec` together with
`HasWeakIteratedLineDerivOn.ae_eq`.) -/
theorem sobolevSpace_iff (u : 𝔼 → ℝ) :
    (∃ v : sobolevSpace N p Ω, SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼)] u) ↔
      MemLp u p (volume.restrict (Ω : Set 𝔼)) ∧ ∃ g : Fin N → 𝔼 → ℝ,
        (∀ i, MemLp (g i) p (volume.restrict (Ω : Set 𝔼))) ∧ ∀ (φ : 𝓓(Ω, ℝ)) (i : Fin N),
          ∫ x in (Ω : Set 𝔼), u x * fderiv ℝ φ x (EuclideanSpace.single i 1)
            = -∫ x in (Ω : Set 𝔼), g i x * φ x := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hs := Ω.isOpen.measurableSet
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨(SobolevMultiIndex.memLp v).ae_eq hv, fun i ↦ partialDeriv v i, fun i ↦ Lp.memLp _,
      fun φ i ↦ ?_⟩
    rw [← partialDeriv_spec v i φ]
    exact setIntegral_congr_ae hs ((ae_restrict_iff' hs).1 (hv.mono fun x hx ↦ by rw [hx]))
  · rintro ⟨hu, g, hgp, hg⟩
    obtain ⟨v, hv, -⟩ := exists_sobolevSpace_of_hasWeakIteratedLineDerivOn hu (g := g)
      (fun i ↦ hasWeakIteratedLineDerivOn_single_of_forall (hu.locallyIntegrableOn hp)
        ((hgp i).locallyIntegrableOn hp) fun φ ↦ hg φ i) hgp
    exact ⟨v, hv⟩


/-! ### Remark 1: `C_c^1` test functions -/

omit [Fact (1 ≤ p)] in
/-- **Remark 1.** In the definition of `W^{1,p}(Ω)` the test functions may be taken in `C_c^1(Ω)`
instead of `C_c^∞(Ω)`: for `u ∈ W^{1,p}(Ω)` and `φ : ℝ^N → ℝ` of class `C^1` with compact
support contained in `Ω`, `∫_Ω u ∂φ/∂x_i = −∫_Ω (∂u/∂x_i) φ` — the identity `partialDeriv_spec`
for a `C_c^1` test function, the backbone's
`HasWeakIteratedLineDerivOn.integral_smul_eq_of_contDiff_one` ("use a sequence of
mollifiers"). `remark_9_1_iff` is the resulting equivalence of the two definitions. -/
theorem remark_9_1 (u : sobolevSpace N p Ω) (i : Fin N) {φ : 𝔼 → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (hφΩ : tsupport φ ⊆ Ω) :
    ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn u x * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = -∫ x in (Ω : Set 𝔼), partialDeriv u i x * φ x := by
  have hs := Ω.isOpen.measurableSet
  have h := (hasWeakIteratedLineDerivOn_partialDeriv u i).integral_smul_eq_of_contDiff_one hφ
    hφc hφΩ
  refine (setIntegral_congr_fun hs fun x _ ↦ ?_).trans (h.trans ?_)
  · rw [smul_eq_mul, mul_comm]
  · congr 1
    exact setIntegral_congr_fun hs fun x _ ↦ by rw [smul_eq_mul, mul_comm]

/-- **Remark 1, as the equivalence of the two definitions.** A function `u : ℝ^N → ℝ` is (almost
everywhere on `Ω`) the function of an element of `W^{1,p}(Ω)` if and only if `u ∈ L^p(Ω)` and
there are `g_1, …, g_N ∈ L^p(Ω)` with `∫_Ω u ∂φ/∂x_i = −∫_Ω g_i φ` for every `φ ∈ C_c^1(Ω)` and
every `i` — the Definition of `W^{1,p}(Ω)` with `C_c^1(Ω)` in place of `C_c^∞(Ω)`
(`sobolevSpace_iff`): every `C_c^∞(Ω)` function is `C_c^1`, and `remark_9_1` gives the
identities for `C_c^1(Ω)` from those for `C_c^∞(Ω)`. -/
theorem remark_9_1_iff (u : 𝔼 → ℝ) :
    (∃ v : sobolevSpace N p Ω, SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼)] u) ↔
      MemLp u p (volume.restrict (Ω : Set 𝔼)) ∧ ∃ g : Fin N → 𝔼 → ℝ,
        (∀ i, MemLp (g i) p (volume.restrict (Ω : Set 𝔼))) ∧
        ∀ φ : 𝔼 → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ Ω → ∀ i : Fin N,
          ∫ x in (Ω : Set 𝔼), u x * fderiv ℝ φ x (EuclideanSpace.single i 1)
            = -∫ x in (Ω : Set 𝔼), g i x * φ x := by
  have hs := Ω.isOpen.measurableSet
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨(SobolevMultiIndex.memLp v).ae_eq hv, fun i ↦ partialDeriv v i, fun i ↦ Lp.memLp _,
      fun φ hφ hφc hφΩ i ↦ ?_⟩
    rw [← remark_9_1 v i hφ hφc hφΩ]
    exact setIntegral_congr_ae hs ((ae_restrict_iff' hs).1 (hv.mono fun x hx ↦ by rw [hx]))
  · rintro ⟨hu, g, hgp, hg⟩
    exact (sobolevSpace_iff u).2 ⟨hu, g, hgp, fun φ i ↦
      hg φ (φ.contDiff.of_le (by simp)) φ.hasCompactSupport φ.tsupport_subset i⟩

/-! ### `H^1(Ω)` -/

/-- **The space `H^1(Ω) = W^{1,2}(Ω)`** of §9.1, a Hilbert space for the scalar product
`(u, v)_{H^1} = ∫_Ω u v + ∑_i ∫_Ω ∂_i u ∂_i v` (`hInner`) and the norm
`(‖u‖_2^2 + ∑ ‖∂_i u‖_2^2)^{1/2}` (`hNorm`), which are the inner product and the norm of the
type. -/
noncomputable abbrev hSpace (N : ℕ) (Ω : Opens (EuclideanSpace ℝ (Fin N))) : Type :=
  sobolevSpace N 2 Ω

/-- **The scalar product of `H^1(Ω)`**: `(u, v)_{H^1} = ∫_Ω u v + ∑_i ∫_Ω ∂_i u ∂_i v`. -/
theorem hInner (u v : hSpace N Ω) :
    inner ℝ u v = (∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x)
      + ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv u i x * partialDeriv v i x := by
  rw [SobolevMultiIndex.inner_eq, integral_finsetSum _ fun α _ ↦ L2.integrable_inner (𝕜 := ℝ)
    (SobolevMultiIndex.weakDeriv u α) (SobolevMultiIndex.weakDeriv v α), MultiIndexLE.sum_univ_one]
  simp only [Real.inner_apply, partialDeriv]
  rfl

/-- **The norm of `H^1(Ω)`**: `‖u‖_{H^1} = (‖u‖_2^2 + ∑_i ‖∂_i u‖_2^2)^{1/2}`. -/
theorem hNorm (u : hSpace N Ω) :
    ‖u‖ = √(‖SobolevMultiIndex.weakDeriv u 0‖ ^ 2 + ∑ i, ‖partialDeriv u i‖ ^ 2) := by
  rw [SobolevMultiIndex.norm_eq_sum (by simp), MultiIndexLE.sum_univ_one, Real.sqrt_eq_rpow]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, partialDeriv]

/-! ### The norm `‖u‖_p + ∑ ‖∂_i u‖_p` -/

/-- **The norm the book equips `W^{1,p}(Ω)` with**: `‖u‖_{W^{1,p}} = ‖u‖_p + ∑_i ‖∂u/∂x_i‖_p`.
It is a norm on the type (`bookNorm_add_le`, `bookNorm_smul`, `bookNorm_eq_zero_iff`), equivalent
to the norm of the type, which is the book's "sometimes equivalent norm"
`(‖u‖_p^p + ∑ ‖∂_i u‖_p^p)^{1/p}` (`bookNorm_equiv`). -/
noncomputable def bookNorm (u : sobolevSpace N p Ω) : ℝ :=
  ‖SobolevMultiIndex.weakDeriv u 0‖ + ∑ i, ‖partialDeriv u i‖

omit [Fact (1 ≤ p)] in
/-- The book's norm is the sum of the `L^p` norms of all the weak derivatives of order `≤ 1`. -/
theorem bookNorm_eq_sum (u : sobolevSpace N p Ω) :
    bookNorm u = ∑ α, ‖SobolevMultiIndex.weakDeriv u α‖ :=
  (MultiIndexLE.sum_univ_one fun α ↦ ‖SobolevMultiIndex.weakDeriv u α‖).symm

/-- The book's norm is nonnegative. -/
theorem bookNorm_nonneg (u : sobolevSpace N p Ω) : 0 ≤ bookNorm u :=
  add_nonneg (norm_nonneg _) (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)

/-- The book's norm is subadditive. -/
theorem bookNorm_add_le (u v : sobolevSpace N p Ω) :
    bookNorm (u + v) ≤ bookNorm u + bookNorm v := by
  simp only [bookNorm_eq_sum, SobolevMultiIndex.weakDeriv_add, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun α _ ↦ norm_add_le _ _

/-- The book's norm is homogeneous. -/
theorem bookNorm_smul (c : ℝ) (u : sobolevSpace N p Ω) : bookNorm (c • u) = |c| * bookNorm u := by
  simp only [bookNorm_eq_sum, SobolevMultiIndex.weakDeriv_smul, norm_smul, Real.norm_eq_abs,
    Finset.mul_sum]

/-- **The two norms of `W^{1,p}(Ω)` are equivalent**: `‖u‖ ≤ ‖u‖_{W^{1,p}} ≤ (N + 1) ‖u‖`, where
`‖u‖` is the norm of the type, `(‖u‖_p^p + ∑ ‖∂_i u‖_p^p)^{1/p}` — the `ℓ^p` and `ℓ^1` norms of
the `N + 1` numbers `‖u‖_p, ‖∂_1 u‖_p, …, ‖∂_N u‖_p`. -/
theorem bookNorm_equiv (u : sobolevSpace N p Ω) :
    ‖u‖ ≤ bookNorm u ∧ bookNorm u ≤ (N + 1) * ‖u‖ := by
  refine ⟨bookNorm_eq_sum u ▸ SobolevMultiIndex.norm_le_sum_norm_weakDeriv u, ?_⟩
  calc bookNorm u = ∑ α, ‖SobolevMultiIndex.weakDeriv u α‖ := bookNorm_eq_sum u
    _ ≤ ∑ _α : MultiIndexLE (Fin N) 1, ‖u‖ :=
        Finset.sum_le_sum fun α _ ↦ SobolevMultiIndex.norm_weakDeriv_le u α
    _ = (N + 1) * ‖u‖ := by
        rw [MultiIndexLE.sum_univ_one (fun _ ↦ ‖u‖)]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- The book's norm vanishes only at `0`. -/
theorem bookNorm_eq_zero_iff (u : sobolevSpace N p Ω) : bookNorm u = 0 ↔ u = 0 := by
  constructor
  · intro h
    exact norm_le_zero_iff.1 ((bookNorm_equiv u).1.trans h.le)
  · rintro rfl
    refine le_antisymm ?_ (bookNorm_nonneg 0)
    simpa using (bookNorm_equiv (0 : sobolevSpace N p Ω)).2

/-! ### Proposition 9.1 -/

/-- **Proposition 9.1, first clause**: `W^{1,p}(Ω)` is a Banach space for every `1 ≤ p ≤ ∞`. -/
theorem proposition_9_1_banach : CompleteSpace (sobolevSpace N p Ω) :=
  inferInstance

/-- **Proposition 9.1, second clause**: `W^{1,p}(Ω)` is reflexive for `1 < p < ∞`, in the
sense of chapter 3's Definition (`Brezis.Chapter03.IsReflexive`), through the reflexivity of
`L^p(Ω)` (Theorem 4.10). -/
theorem proposition_9_1_reflexive (hp : 1 < p) (hp' : p ≠ ⊤) :
    Chapter03.IsReflexive (sobolevSpace N p Ω) := by
  have := Chapter04.theorem_4_10 (μ := volume.restrict (Ω : Set 𝔼)) hp hp'
  exact Chapter03.isReflexive_iff.2 inferInstance

/-- **Proposition 9.1, third clause**: `W^{1,p}(Ω)` is separable for `1 ≤ p < ∞`, in the sense
of chapter 3's Definition (`Brezis.Chapter03.IsSeparable`). -/
theorem proposition_9_1_separable (hp' : p ≠ ⊤) : Chapter03.IsSeparable (sobolevSpace N p Ω) := by
  have := Fact.mk hp'
  exact (Chapter03.separable_iff _).2 inferInstance

/-- **Proposition 9.1, last clause**: `H^1(Ω)` is a separable Hilbert space — its inner product
is the instance of the type (`hInner`), and it is complete and separable. -/
theorem proposition_9_1_hilbert :
    CompleteSpace (hSpace N Ω) ∧ Chapter03.IsSeparable (hSpace N Ω) :=
  ⟨proposition_9_1_banach, proposition_9_1_separable (by simp)⟩

/-- **Proposition 9.1.** `W^{1,p}(Ω)` is a Banach space for every `1 ≤ p ≤ ∞`; it is reflexive
for `1 < p < ∞` and separable for `1 ≤ p < ∞`; `H^1(Ω)` is a separable Hilbert space. The
proof is the backbone's: `W^{1,p}(Ω)` is a closed subspace of the `ℓ^p` product of `N + 1` copies
of `L^p(Ω)`, the operator `T u = [u, ∇u]` of the book's proof of Proposition 8.1 being the
inclusion. -/
theorem proposition_9_1 :
    CompleteSpace (sobolevSpace N p Ω) ∧
    (1 < p → p ≠ ⊤ → Chapter03.IsReflexive (sobolevSpace N p Ω)) ∧
    (p ≠ ⊤ → Chapter03.IsSeparable (sobolevSpace N p Ω)) ∧
    (CompleteSpace (hSpace N Ω) ∧ Chapter03.IsSeparable (hSpace N Ω)) :=
  ⟨proposition_9_1_banach, proposition_9_1_reflexive, proposition_9_1_separable,
    proposition_9_1_hilbert⟩

/-! ### The tensor gradient -/

omit [Fact (1 ≤ p)] in
/-- The gradient of `u ∈ W^{1,p}(Ω)` is almost everywhere strongly measurable on `Ω`. -/
theorem aestronglyMeasurable_gradient (u : sobolevSpace N p Ω) :
    AEStronglyMeasurable (gradient u) (volume.restrict (Ω : Set 𝔼)) :=
  (PiLp.continuous_toLp 2 _).comp_aestronglyMeasurable
    (aemeasurable_pi_iff.2 fun i ↦
      (Lp.aestronglyMeasurable (partialDeriv u i)).aemeasurable).aestronglyMeasurable

/-- A continuous linear functional on `ℝ^N` is the inner product with the vector of its values on
the standard basis, and its norm is the Euclidean norm of that vector. -/
theorem norm_eq_norm_toLp_apply_single (L : 𝔼 →L[ℝ] ℝ) :
    ‖L‖ = ‖(WithLp.toLp 2 fun i ↦ L (EuclideanSpace.single i 1) : 𝔼)‖ := by
  have h : L = innerSL ℝ (E := 𝔼) (WithLp.toLp 2 fun i ↦ L (EuclideanSpace.single i 1)) := by
    refine ContinuousLinearMap.coe_injective ((𝔟).ext fun i ↦ ?_)
    simp [EuclideanSpace.inner_single_right]
  conv_lhs => rw [h]
  exact innerSL_apply_norm (𝕜 := ℝ) (E := 𝔼) _

/-- **The tensor weak derivative of `u ∈ W^{1,p}(Ω)`**: a first-order weak derivative
`w : ℝ^N → (ℝ^N →L[ℝ] ℝ)` of `u` on `Ω`, in `L^p(Ω)`, whose values on the basis vectors are the
partial derivatives `∂u/∂x_i`, whose operator norm is the Euclidean norm `|∇u|` of the gradient
almost everywhere on `Ω`, and whose `L^p(Ω)` norm is therefore `‖∇u‖_{L^p(Ω)}`. -/
theorem exists_hasWeakFDerivOn_fn_gradient (u : sobolevSpace N p Ω) :
    ∃ w : 𝔼 → 𝔼 →L[ℝ] ℝ, HasWeakFDerivOn (SobolevMultiIndex.fn u) w Ω volume ∧
      MemLp w p (volume.restrict (Ω : Set 𝔼)) ∧
      (∀ i, (fun x ↦ w x (EuclideanSpace.single i 1)) =ᵐ[volume.restrict (Ω : Set 𝔼)]
        partialDeriv u i) ∧
      (∀ᵐ x ∂volume.restrict (Ω : Set 𝔼), ‖w x‖ = ‖gradient u x‖) ∧
      eLpNorm w p (volume.restrict (Ω : Set 𝔼)) = eLpNorm (gradient u) p (volume.restrict Ω) := by
  obtain ⟨w, hw, hwp, hwi, -⟩ := SobolevMultiIndex.exists_hasWeakFDerivOn_fn (b := 𝔟) u
  have hwi' : ∀ i, (fun x ↦ w x (EuclideanSpace.single i 1)) =ᵐ[volume.restrict (Ω : Set 𝔼)]
      partialDeriv u i := fun i ↦ by
    have := hwi i
    rwa [basisFun_toBasis_apply] at this
  have hnorm : ∀ᵐ x ∂volume.restrict (Ω : Set 𝔼), ‖w x‖ = ‖gradient u x‖ := by
    filter_upwards [ae_all_iff.2 hwi'] with x hx
    rw [norm_eq_norm_toLp_apply_single (w x)]
    congr 2
    funext i
    exact hx i
  refine ⟨w, hw, hwp, hwi', hnorm, ?_⟩
  exact eLpNorm_congr_norm_ae hwp.aestronglyMeasurable (aestronglyMeasurable_gradient u) hnorm

/-- The gradient of `u ∈ W^{1,p}(Ω)` lies in `L^p(Ω)`. -/
theorem memLp_gradient (u : sobolevSpace N p Ω) :
    MemLp (gradient u) p (volume.restrict (Ω : Set 𝔼)) := by
  obtain ⟨w, -, hwp, -, -, heq⟩ := exists_hasWeakFDerivOn_fn_gradient u
  rw [memLp_iff, ← heq]
  exact hwp

/-! ### Remark 2: `C^1` functions -/

/-- **Remark 2, first part.** If `u ∈ C^1(Ω) ∩ L^p(Ω)` and its classical partial derivatives
`∂u/∂x_i = ∂_{e_i} u` lie in `L^p(Ω)`, then `u` is (almost everywhere on `Ω`) the function of an
element of `W^{1,p}(Ω)`, whose weak partial derivatives are the classical ones: the notation is
consistent. -/
theorem remark_9_2 {u : 𝔼 → ℝ} (hu : ContDiffOn ℝ 1 u Ω) (hup : MemLp u p (volume.restrict Ω))
    (hd : ∀ i, MemLp (fun x ↦ fderiv ℝ u x (EuclideanSpace.single i 1)) p (volume.restrict Ω)) :
    ∃ v : sobolevSpace N p Ω, SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼)] u ∧
      ∀ i, partialDeriv v i =ᵐ[volume.restrict (Ω : Set 𝔼)]
        fun x ↦ fderiv ℝ u x (EuclideanSpace.single i 1) := by
  refine exists_sobolevSpace_of_hasWeakIteratedLineDerivOn hup (fun i ↦ ?_) hd
  have h := (hu.hasWeakIteratedFDerivOn (μ := volume) (m := 1) le_rfl).lineDeriv
    ![EuclideanSpace.single i 1]
  simpa [iteratedFDeriv_one_apply] using h

/-- **Remark 2, "in particular"**: if `Ω` is bounded, every `u ∈ C^1(Ω̄)` (here: of class `C^1`
on `closure Ω`) is the function of an element of `W^{1,p}(Ω)`, for every `1 ≤ p ≤ ∞`: `u` and
its derivative are bounded on `Ω`, and `Ω` has finite measure. -/
theorem remark_9_2_closure (hΩ : Bornology.IsBounded (Ω : Set 𝔼)) {u : 𝔼 → ℝ}
    (hu : ContDiffOn ℝ 1 u (closure Ω)) :
    ∃ v : sobolevSpace N p Ω, SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼)] u := by
  have hs := Ω.isOpen.measurableSet
  have : IsFiniteMeasure (volume.restrict (Ω : Set 𝔼)) :=
    ⟨by simpa [Measure.restrict_apply_univ] using hΩ.measure_lt_top⟩
  have hΩc : IsCompact (closure (Ω : Set 𝔼)) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hΩ.closure
  have hu' : ContDiffOn ℝ 1 u Ω := hu.mono subset_closure
  obtain ⟨C, hC⟩ := hΩc.exists_bound_of_continuousOn hu.continuousOn
  obtain ⟨M, hM⟩ := hu.exists_norm_fderiv_le_of_isCompact hΩc
  have hΩi : (Ω : Set 𝔼) ⊆ interior (closure (Ω : Set 𝔼)) :=
    Ω.isOpen.subset_interior_iff.2 subset_closure
  have hup : MemLp u p (volume.restrict Ω) :=
    MemLp.of_bound (hu'.continuousOn.aestronglyMeasurable hs) C
      ((ae_restrict_iff' hs).2 (Eventually.of_forall fun x hx ↦ hC x (subset_closure hx)))
  have hd : ∀ i, MemLp (fun x ↦ fderiv ℝ u x (EuclideanSpace.single i 1)) p
      (volume.restrict Ω) := fun i ↦
    MemLp.of_bound (((hu'.continuousOn_fderiv_of_isOpen Ω.isOpen le_rfl).clm_apply
      continuousOn_const).aestronglyMeasurable hs) M
      ((ae_restrict_iff' hs).2 (Eventually.of_forall fun x hx ↦ by
        calc ‖fderiv ℝ u x (EuclideanSpace.single i 1)‖
            ≤ ‖fderiv ℝ u x‖ * ‖(EuclideanSpace.single i (1 : ℝ) : 𝔼)‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ M := by simpa using hM x (hΩi hx)))
  obtain ⟨v, hv, -⟩ := remark_9_2 hu' hup hd
  exact ⟨v, hv⟩

/-- **Remark 2, converse.** If `u ∈ W^{1,p}(Ω)` and each weak partial derivative `∂u/∂x_i` has
a representative `g_i` continuous on `Ω`, then `u ∈ C^1(Ω)`: more precisely, there is
`ũ ∈ C^1(Ω)` with `u = ũ` almost everywhere on `Ω`, whose partial derivatives are the `g_i`. -/
theorem remark_9_2_converse (u : sobolevSpace N p Ω) {g : Fin N → 𝔼 → ℝ}
    (hg : ∀ i, ContinuousOn (g i) Ω)
    (hgu : ∀ i, partialDeriv u i =ᵐ[volume.restrict (Ω : Set 𝔼)] g i) :
    ∃ ũ : 𝔼 → ℝ, ContDiffOn ℝ 1 ũ Ω ∧ SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ ∧
      ∀ x ∈ (Ω : Set 𝔼), ∀ i, fderiv ℝ ũ x (EuclideanSpace.single i 1) = g i x := by
  have hs := Ω.isOpen.measurableSet
  obtain ⟨w, hw, -, hwi, -, -⟩ := exists_hasWeakFDerivOn_fn_gradient u
  -- the continuous tensor gradient assembled from the `g_i`
  set W : 𝔼 → 𝔼 →L[ℝ] ℝ := fun x ↦ innerSL ℝ (E := 𝔼) (WithLp.toLp 2 fun i ↦ g i x)
    with hWdef
  have hWi : ∀ x i, W x (EuclideanSpace.single i 1) = g i x := fun x i ↦ by
    simp [hWdef, EuclideanSpace.inner_single_right]
  have hWc : ContinuousOn W Ω := by
    refine (innerSL ℝ).continuous.comp_continuousOn
      ((PiLp.continuous_toLp 2 _).comp_continuousOn (continuousOn_pi.2 fun i ↦ hg i))
  have hwW : w =ᵐ[volume.restrict (Ω : Set 𝔼)] W := by
    filter_upwards [ae_all_iff.2 fun i ↦ (hwi i).trans (hgu i)] with x hx
    refine ContinuousLinearMap.coe_injective ((𝔟).ext fun i ↦ ?_)
    rw [basisFun_toBasis_apply]
    simpa [hWi] using hx i
  have hW : HasWeakFDerivOn (SobolevMultiIndex.fn u) W Ω volume :=
    HasWeakIteratedFDerivOn.congr_ae hw (Filter.EventuallyEq.refl _ _)
      (hwW.mono fun x hx ↦ by simp only [hx])
  obtain ⟨ũ, hũ, hu, hd⟩ := hW.exists_contDiffOn_ae_eq_of_continuousOn hWc
  exact ⟨ũ, hũ, hu, fun x hx i ↦ by rw [(hd x hx).fderiv, hWi]⟩


/-! ### Convergence in `W^{1,p}(Ω)` -/

/-- The `L^p(Ω)` distance between the function of `u ∈ W^{1,p}(Ω)` and `f ∈ L^p(Ω)` is the
distance of the elements of `L^p(Ω)`. -/
theorem eLpNorm_fn_sub_eq (u : sobolevSpace N p Ω) (f : Lp ℝ p (volume.restrict (Ω : Set 𝔼))) :
    eLpNorm (SobolevMultiIndex.fn u - ⇑f) p (volume.restrict (Ω : Set 𝔼))
      = ENNReal.ofReal ‖SobolevMultiIndex.fnL ℝ 𝔟 1 p Ω volume u - f‖ := by
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _),
    eLpNorm_congr_ae (Lp.coeFn_sub _ _), SobolevMultiIndex.fnL_apply]

/-- Convergence in `W^{1,p}(Ω)` implies convergence of the functions in `L^p(Ω)`, in the
`eLpNorm` form. -/
theorem tendsto_eLpNorm_fn_sub_of_tendsto {u : ℕ → sobolevSpace N p Ω}
    {f : Lp ℝ p (volume.restrict (Ω : Set 𝔼))}
    (hf : Tendsto (fun n ↦ SobolevMultiIndex.fnL ℝ 𝔟 1 p Ω volume (u n)) atTop (𝓝 f)) :
    Tendsto (fun n ↦ eLpNorm (SobolevMultiIndex.fn (u n) - ⇑f) p (volume.restrict (Ω : Set 𝔼)))
      atTop (𝓝 0) := by
  simp only [eLpNorm_fn_sub_eq]
  rw [← ENNReal.ofReal_zero]
  exact ENNReal.tendsto_ofReal (tendsto_iff_norm_sub_tendsto_zero.1 hf)

/-- **Convergence in `W^{1,p}(Ω)` from convergence of the tensor Sobolev norms**: if
`fn (w n) = v n` almost everywhere on `Ω` and `sobolevNorm (v n − fn u) → 0`, then `w n → u` in
`W^{1,p}(Ω)`, by the comparison `SobolevMultiIndex.ofReal_norm_le_sobolevNorm` of the two
norms. -/
theorem tendsto_of_tendsto_sobolevNorm (hp' : p ≠ ⊤) {w : ℕ → sobolevSpace N p Ω}
    {u : sobolevSpace N p Ω} {v : ℕ → 𝔼 → ℝ}
    (hw : ∀ n, SobolevMultiIndex.fn (w n) =ᵐ[volume.restrict (Ω : Set 𝔼)] v n)
    (h : Tendsto (fun n ↦ sobolevNorm (v n - SobolevMultiIndex.fn u) 1 p Ω volume) atTop
      (𝓝 0)) :
    Tendsto w atTop (𝓝 u) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsub : ∀ n, sobolevNorm (SobolevMultiIndex.fn (w n - u)) 1 p Ω volume
      = sobolevNorm (v n - SobolevMultiIndex.fn u) 1 p Ω volume := fun n ↦
    sobolevNorm_congr_ae ((SobolevMultiIndex.fn_sub _ _).trans
      ((hw n).sub (Filter.EventuallyEq.refl _ _)))
  obtain ⟨C, hC, hCle⟩ : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ n, ENNReal.ofReal ‖w n - u‖
      ≤ C * sobolevNorm (v n - SobolevMultiIndex.fn u) 1 p Ω volume := by
    refine ⟨_, ?_, fun n ↦ by
      rw [← hsub n]
      exact SobolevMultiIndex.ofReal_norm_le_sobolevNorm hp' (w n - u)⟩
    exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.sum_ne_top.2 fun _ _ ↦ enorm_ne_top⟩
  have hfin : ∀ᶠ n in atTop, sobolevNorm (v n - SobolevMultiIndex.fn u) 1 p Ω volume ≠ ⊤ := by
    filter_upwards [ENNReal.tendsto_nhds_zero.1 h 1 one_pos] with n hn
    exact (hn.trans_lt ENNReal.one_lt_top).ne
  have hbound : ∀ n, sobolevNorm (v n - SobolevMultiIndex.fn u) 1 p Ω volume ≠ ⊤ →
      ‖w n - u‖ ≤ (C * sobolevNorm (v n - SobolevMultiIndex.fn u) 1 p Ω volume).toReal :=
    fun n hn ↦ (ENNReal.toReal_ofReal (norm_nonneg _)).symm.le.trans
      (ENNReal.toReal_mono (ENNReal.mul_ne_top hC hn) (hCle n))
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) (hfin.mono hbound) ?_
  have h1 : Tendsto (fun n ↦ C * sobolevNorm (v n - SobolevMultiIndex.fn u) 1 p Ω volume) atTop
      (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul h (Or.inr hC)
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
  simpa [Function.comp_def] using this

/-! ### Remark 4 -/

/-- **Remark 4 (i), first sentence.** If `u_n ∈ W^{1,p}(Ω)`, `u_n → f` in `L^p(Ω)` and
`∇u_n` converges in `(L^p(Ω))^N`, to `(g_1, …, g_N)`, then `f ∈ W^{1,p}(Ω)` — it is the function of
an element `v` with `∂v/∂x_i = g_i` — and `‖u_n − v‖_{W^{1,p}} → 0`. This is the closedness of
`W^{1,p}(Ω)` in the product of `N + 1` copies of `L^p(Ω)`, the argument of the proof of
Proposition 9.1. -/
theorem remark_9_4_i {u : ℕ → sobolevSpace N p Ω} {f : Lp ℝ p (volume.restrict (Ω : Set 𝔼))}
    {g : Fin N → Lp ℝ p (volume.restrict (Ω : Set 𝔼))}
    (hf : Tendsto (fun n ↦ SobolevMultiIndex.fnL ℝ 𝔟 1 p Ω volume (u n)) atTop (𝓝 f))
    (hg : ∀ i, Tendsto (fun n ↦ partialDeriv (u n) i) atTop (𝓝 (g i))) :
    ∃ v : sobolevSpace N p Ω, SobolevMultiIndex.fnL ℝ 𝔟 1 p Ω volume v = f ∧
      (∀ i, partialDeriv v i = g i) ∧ Tendsto u atTop (𝓝 v) := by
  classical
  -- the limit family in the ambient `ℓ^p` product of `L^p(Ω)` spaces
  let F : MultiIndexLE (Fin N) 1 → Lp ℝ p (volume.restrict (Ω : Set 𝔼)) := fun α ↦
    if h : ∃ i, α = MultiIndexLE.single i then g h.choose else f
  have hF0 : F 0 = f := by
    have h : ¬ ∃ i, (0 : MultiIndexLE (Fin N) 1) = MultiIndexLE.single i :=
      fun ⟨i, hi⟩ ↦ MultiIndexLE.single_ne_zero i hi.symm
    simp only [F, h, ↓reduceDIte]
  have hFi : ∀ i, F (MultiIndexLE.single i) = g i := fun i ↦ by
    have h : ∃ j, MultiIndexLE.single i = MultiIndexLE.single j := ⟨i, rfl⟩
    simp only [F, h, ↓reduceDIte]
    exact congrArg g (MultiIndexLE.single_injective h.choose_spec).symm
  have htend : Tendsto (fun n ↦ (u n : SobolevMultiIndexTuple ℝ (Fin N) 1 p Ω volume)) atTop
      (𝓝 (WithLp.toLp p F)) := by
    have h1 : Tendsto (fun n ↦ WithLp.ofLp (u n : SobolevMultiIndexTuple ℝ (Fin N) 1 p Ω volume))
        atTop (𝓝 F) := by
      refine tendsto_pi_nhds.2 fun α ↦ ?_
      rcases MultiIndexLE.eq_zero_or_exists_eq_single α with rfl | ⟨i, rfl⟩
      · rw [hF0]
        have h := hf
        simp only [SobolevMultiIndex.fnL_eq_weakDeriv_zero] at h
        exact h
      · rw [hFi]
        exact hg i
    have h2 := ((PiLp.continuous_toLp p _).tendsto F).comp h1
    simpa [Function.comp_def] using h2
  have hmem : WithLp.toLp p F ∈ SobolevMultiIndex ℝ 𝔟 1 p Ω volume :=
    SobolevMultiIndex.isClosed.mem_of_tendsto htend (Eventually.of_forall fun n ↦ (u n).2)
  refine ⟨⟨WithLp.toLp p F, hmem⟩, ?_, fun i ↦ ?_, tendsto_subtype_rng.2 htend⟩
  · rw [SobolevMultiIndex.fnL_eq_weakDeriv_zero]
    exact hF0
  · exact hFi i

/-- **Remark 4 (i), second sentence.** When `1 < p ≤ ∞` it suffices to know that `u_n → f` in
`L^p(Ω)` and that `(∇u_n)` is bounded in `(L^p(Ω))^N` to conclude that `f ∈ W^{1,p}(Ω)`: the
bound (ii) of Proposition 9.3 for the `u_n` passes to the limit and (ii) ⇒ (i) applies (the
book's "why?"). Here `q` is the conjugate exponent of `p`, and `1 < p` makes `q < ∞`. -/
theorem remark_9_4_i_bounded {q : ℝ≥0∞} [p.HolderConjugate q] (hp : 1 < p)
    {u : ℕ → sobolevSpace N p Ω} {f : Lp ℝ p (volume.restrict (Ω : Set 𝔼))}
    (hf : Tendsto (fun n ↦ SobolevMultiIndex.fnL ℝ 𝔟 1 p Ω volume (u n)) atTop (𝓝 f))
    {M : ℝ} (hM : ∀ n i, ‖partialDeriv (u n) i‖ ≤ M) :
    ∃ v : sobolevSpace N p Ω, SobolevMultiIndex.fnL ℝ 𝔟 1 p Ω volume v = f := by
  have hq : q ≠ ⊤ :=
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt (p := q) (q := p)).2 hp).ne
  choose w hw hwp hwi hwb using fun n ↦ SobolevMultiIndex.exists_hasWeakFDerivOn_fn (b := 𝔟) (u n)
  obtain ⟨Cb, hCb⟩ : ∃ Cb : ℝ, Cb = Fintype.card (Fin N) •
    ‖(𝔟).equivFunL.toContinuousLinearMap‖ := ⟨_, rfl⟩
  have hwM : ∀ n, eLpNorm (w n) p (volume.restrict (Ω : Set 𝔼))
      ≤ ENNReal.ofReal Cb * (N * ENNReal.ofReal M) := fun n ↦ by
    refine (hwb n).trans ?_
    rw [hCb]
    gcongr
    calc ∑ i, eLpNorm (SobolevMultiIndex.weakDeriv (u n) (MultiIndexLE.single i)) p
          (volume.restrict (Ω : Set 𝔼))
        = ∑ i, ENNReal.ofReal ‖partialDeriv (u n) i‖ := Finset.sum_congr rfl fun i _ ↦ by
          rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
          rfl
      _ ≤ ∑ _i : Fin N, ENNReal.ofReal M :=
          Finset.sum_le_sum fun i _ ↦ ENNReal.ofReal_le_ofReal (hM n i)
      _ = N * ENNReal.ofReal M := by simp
  have hmem : MemSobolev (f : 𝔼 → ℝ) 1 p Ω volume :=
    MemSobolev.of_tendsto_eLpNorm_of_eLpNorm_le hq (fun n ↦ SobolevMultiIndex.memLp (u n)) hw
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top))
      hwM (Lp.memLp f) (tendsto_eLpNorm_fn_sub_of_tendsto hf)
  obtain ⟨v, hv⟩ := hmem.memSobolevMultiIndex.exists_sobolevMultiIndex (b := 𝔟)
  refine ⟨v, Lp.ext ?_⟩
  rw [SobolevMultiIndex.fnL_apply]
  exact hv

/-- **Remark 4 (ii), general form (the remark's last sentence).** Let `u ∈ W^{1,p}(Ω)` and let
`α` be smooth and bounded with bounded gradient, with `supp α ⊆ ℝ^N ∖ ∂Ω` (the backbone's
`IsSobolevCutoff Ω α`, with `C^∞` in place of the book's `C^1`). Then the extension by zero
`\overline{α u}` of `α u` outside `Ω` lies in `W^{1,p}(ℝ^N)`, with
`∂_i \overline{α u} = \overline{α ∂_i u + (∂_i α) u}`. -/
theorem remark_9_4_ii_cutoff (u : sobolevSpace N p Ω) {α : 𝔼 → ℝ} (hα : IsSobolevCutoff Ω α) :
    ∃ v : sobolevSpace N p ⊤,
      SobolevMultiIndex.fn v =ᵐ[volume]
        (Ω : Set 𝔼).indicator (fun x ↦ α x * SobolevMultiIndex.fn u x) ∧
      ∀ i, partialDeriv v i =ᵐ[volume] (Ω : Set 𝔼).indicator fun x ↦
        α x * partialDeriv u i x
          + fderiv ℝ α x (EuclideanSpace.single i 1) * SobolevMultiIndex.fn u x := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hmem := (SobolevMultiIndex.memSobolevMultiIndex u).indicator_mul hp hα
  have hg : ∀ i, HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1]
      ((Ω : Set 𝔼).indicator fun x ↦ α x * SobolevMultiIndex.fn u x)
      ((Ω : Set 𝔼).indicator fun x ↦ α x * partialDeriv u i x
        + fderiv ℝ α x (EuclideanSpace.single i 1) * SobolevMultiIndex.fn u x) ⊤ volume :=
    fun i ↦ (hasWeakIteratedLineDerivOn_partialDeriv u i).indicator_mul hα
  obtain ⟨v, hv, hvi⟩ := exists_sobolevSpace_of_hasWeakIteratedLineDerivOn hmem.memLp hg
    fun i ↦ memLp_of_memSobolevMultiIndex_of_hasWeakIteratedLineDerivOn hmem (hg i)
  exact ⟨v, eventuallyEq_restrict_coe_top_iff.1 hv,
    fun i ↦ eventuallyEq_restrict_coe_top_iff.1 (hvi i)⟩

/-- **Remark 4 (ii).** Let `u ∈ W^{1,p}(Ω)` and let `α` be smooth with compact support in `Ω`
(the book's `α ∈ C_c^1(Ω)`, with `C^∞` in place of `C^1`). Then the extension by zero
`\overline{α u}` of `α u` outside `Ω` lies in `W^{1,p}(ℝ^N)`, with
`∂_i \overline{α u} = \overline{α ∂_i u + (∂_i α) u}`. -/
theorem remark_9_4_ii (u : sobolevSpace N p Ω) {α : 𝔼 → ℝ} (hα : ContDiff ℝ ∞ α)
    (hαc : HasCompactSupport α) (hαΩ : tsupport α ⊆ Ω) :
    ∃ v : sobolevSpace N p ⊤,
      SobolevMultiIndex.fn v =ᵐ[volume]
        (Ω : Set 𝔼).indicator (fun x ↦ α x * SobolevMultiIndex.fn u x) ∧
      ∀ i, partialDeriv v i =ᵐ[volume] (Ω : Set 𝔼).indicator fun x ↦
        α x * partialDeriv u i x
          + fderiv ℝ α x (EuclideanSpace.single i 1) * SobolevMultiIndex.fn u x :=
  remark_9_4_ii_cutoff u (IsSobolevCutoff.of_hasCompactSupport hα hαc hαΩ)

/-! ### Strong inclusion, and Friedrichs' theorem -/

/-- **The Definition of `ω ⊂⊂ Ω`**: an open set `ω` is *strongly included* in `Ω` if `ω̄ ⊆ Ω`
and `ω̄` is compact (footnote 4: the closure is taken in `ℝ^N`). -/
def IsStronglyIncluded (V Ω : Set 𝔼) : Prop :=
  IsOpen V ∧ closure V ⊆ Ω ∧ IsCompact (closure V)

@[inherit_doc] scoped[Brezis] infixl:50 " ⊂⊂ " => Brezis.Chapter09.IsStronglyIncluded

/-- A strongly included set is a subset. -/
theorem IsStronglyIncluded.subset {V Ω : Set 𝔼} (h : IsStronglyIncluded V Ω) : V ⊆ Ω :=
  subset_closure.trans h.2.1

/-- **Theorem 9.2 (Friedrichs).** Let `u ∈ W^{1,p}(Ω)` with `1 ≤ p < ∞`. Then there is a
sequence `(u_n)` from `C_c^∞(ℝ^N)` such that `u_n|_Ω → u` in `L^p(Ω)` and
`∇u_n|_ω → ∇u|_ω` in `L^p(ω)^N` for every `ω ⊂⊂ Ω` — component by component, for every `i`.
The backbone theorem `MemSobolev.exists_seq_contDiff_hasCompactSupport_tendsto` is stated with
the tensor gradient, of which the partial derivatives are the values on the basis vectors
(`exists_hasWeakFDerivOn_fn_gradient`). -/
theorem theorem_9_2 (hp' : p ≠ ⊤) (u : sobolevSpace N p Ω) :
    ∃ v : ℕ → 𝔼 → ℝ, (∀ n, ContDiff ℝ ∞ (v n)) ∧ (∀ n, HasCompactSupport (v n)) ∧
      Tendsto (fun n ↦ eLpNorm (v n - SobolevMultiIndex.fn u) p (volume.restrict (Ω : Set 𝔼)))
        atTop (𝓝 0) ∧
      ∀ V : Set 𝔼, IsStronglyIncluded V Ω → ∀ i,
        Tendsto (fun n ↦ eLpNorm (fun x ↦ fderiv ℝ (v n) x (EuclideanSpace.single i 1)
          - partialDeriv u i x) p (volume.restrict V)) atTop (𝓝 0) := by
  have hf : MemSobolev (SobolevMultiIndex.fn u) 1 p Ω volume :=
    (SobolevMultiIndex.memSobolevMultiIndex u).memSobolev
  obtain ⟨v, hvs, hvc, hv0, hv1⟩ := hf.exists_seq_contDiff_hasCompactSupport_tendsto Fact.out hp'
  obtain ⟨w, hw, hwp, hwi, -, -⟩ := exists_hasWeakFDerivOn_fn_gradient u
  refine ⟨v, hvs, hvc, hv0, fun V hV i ↦ ?_⟩
  have hVΩ : V ⊆ (Ω : Set 𝔼) := hV.subset
  have hVt := hv1 w hw V hV.2.2 hV.2.1
  have hwi' : (fun x ↦ w x (EuclideanSpace.single i 1)) =ᵐ[volume.restrict V] partialDeriv u i :=
    (hwi i).filter_mono (ae_mono (Measure.restrict_mono hVΩ le_rfl))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hVt (fun _ ↦ zero_le)
    fun n ↦ ?_
  calc eLpNorm (fun x ↦ fderiv ℝ (v n) x (EuclideanSpace.single i 1) - partialDeriv u i x) p
        (volume.restrict V)
      = eLpNorm (fun x ↦ ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ) : 𝔼)
          (fderiv ℝ (v n) x - w x)) p (volume.restrict V) := by
        refine eLpNorm_congr_ae (hwi'.mono fun x hx ↦ ?_)
        simp only [ContinuousLinearMap.apply_apply, sub_apply]
        rw [← hx]
    _ ≤ ‖ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ) : 𝔼)‖ₑ
          * eLpNorm (fun x ↦ fderiv ℝ (v n) x - w x) p (volume.restrict V) :=
        eLpNorm_comp_continuousLinearMap_le _ _ p
    _ ≤ 1 * eLpNorm (fun x ↦ fderiv ℝ (v n) x - w x) p (volume.restrict V) := by
        gcongr
        rw [← ofReal_norm, ← ENNReal.ofReal_one]
        refine ENNReal.ofReal_le_ofReal ((ContinuousLinearMap.opNorm_le_bound _ zero_le_one
          fun L ↦ ?_))
        rw [one_mul, ContinuousLinearMap.apply_apply]
        simpa using L.le_opNorm (EuclideanSpace.single i (1 : ℝ) : 𝔼)
    _ = eLpNorm (fun x ↦ fderiv ℝ (v n) x - w x) p (volume.restrict V) := one_mul _

/-- **Theorem 9.2, the case `Ω = ℝ^N`.** For `u ∈ W^{1,p}(ℝ^N)`, `1 ≤ p < ∞`, there is a
sequence `(u_n)` from `C_c^∞(ℝ^N)` with `u_n → u` in `L^p(ℝ^N)` and `∇u_n → ∇u` in
`L^p(ℝ^N)^N`, that is, `u_n → u` in `W^{1,p}(ℝ^N)`: the elements `w n` of `W^{1,p}(ℝ^N)` whose
functions are the `u_n` converge to `u`. -/
theorem theorem_9_2_univ (hp' : p ≠ ⊤) (u : sobolevSpace N p ⊤) :
    ∃ v : ℕ → 𝔼 → ℝ, (∀ n, ContDiff ℝ ∞ (v n)) ∧ (∀ n, HasCompactSupport (v n)) ∧
      ∃ w : ℕ → sobolevSpace N p ⊤, (∀ n, SobolevMultiIndex.fn (w n) =ᵐ[volume] v n) ∧
        Tendsto w atTop (𝓝 u) := by
  have hf : MemSobolev (SobolevMultiIndex.fn u) 1 p ⊤ volume :=
    (SobolevMultiIndex.memSobolevMultiIndex u).memSobolev
  obtain ⟨v, hvs, hvc, hvt⟩ := hf.exists_seq_hasCompactSupport_tendsto_sobolevNorm Fact.out hp'
  choose w hw using fun n ↦ (hvs n).exists_sobolevMultiIndex_of_hasCompactSupport (b := 𝔟)
    (k := 1) (p := p) (Ω := (⊤ : Opens 𝔼)) (μ := volume) (hvc n)
  exact ⟨v, hvs, hvc, w, fun n ↦ eventuallyEq_restrict_coe_top_iff.1 (hw n),
    tendsto_of_tendsto_sobolevNorm hp' hw hvt⟩

/-- **Lemma 9.1.** Let `ρ ∈ L^1(ℝ^N)` and `v ∈ W^{1,p}(ℝ^N)`, `1 ≤ p ≤ ∞`. Then
`ρ ⋆ v ∈ W^{1,p}(ℝ^N)` and `∂_i (ρ ⋆ v) = ρ ⋆ ∂_i v` for every `i`. The convolution is the
book's `(ρ ⋆ v)(x) = ∫ ρ(x − y) v(y) dy`, written as in §4.4. -/
theorem lemma_9_1 {ρ : 𝔼 → ℝ} (hρ : Integrable ρ volume) (v : sobolevSpace N p ⊤) :
    ∃ w : sobolevSpace N p ⊤,
      SobolevMultiIndex.fn w =ᵐ[volume]
        ρ ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] SobolevMultiIndex.fn v ∧
      ∀ i, partialDeriv w i =ᵐ[volume]
        ρ ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] partialDeriv v i := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hv : MemSobolev (SobolevMultiIndex.fn v) 1 p ⊤ volume :=
    (SobolevMultiIndex.memSobolevMultiIndex v).memSobolev
  have hvp : MemLp (SobolevMultiIndex.fn v) p volume := by
    simpa [Measure.restrict_coe_top] using SobolevMultiIndex.memLp v
  have hρ1 : MemLp ρ 1 volume := memLp_one_iff_integrable.2 hρ
  rw [← Chapter04.lsmul_eq_mul_real]
  have hmem := hv.convolution_of_integrable hρ hp
  have hg : ∀ i, HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1]
      (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] SobolevMultiIndex.fn v)
      (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] partialDeriv v i) ⊤ volume := fun i ↦
    (hasWeakIteratedLineDerivOn_partialDeriv v i).convolution_of_integrable hρ hp hvp
      (by simpa [Measure.restrict_coe_top] using Lp.memLp (partialDeriv v i))
  have hgp : ∀ i, MemLp (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] partialDeriv v i) p
      (volume.restrict ((⊤ : Opens 𝔼) : Set 𝔼)) := fun i ↦ by
    rw [Chapter04.lsmul_eq_mul_real]
    have := MemLp.convolution (L := ContinuousLinearMap.mul ℝ ℝ) hp hρ1
      (g := ⇑(partialDeriv v i))
      (by simpa [Measure.restrict_coe_top] using Lp.memLp (partialDeriv v i))
    simpa [Measure.restrict_coe_top] using this
  obtain ⟨w, hw, hwi⟩ := exists_sobolevSpace_of_hasWeakIteratedLineDerivOn hmem.memLp hg hgp
  exact ⟨w, eventuallyEq_restrict_coe_top_iff.1 hw,
    fun i ↦ eventuallyEq_restrict_coe_top_iff.1 (hwi i)⟩

/-- **Remark 5 (Meyers–Serrin).** For `u ∈ W^{1,p}(Ω)`, `1 ≤ p < ∞`, there is a sequence
`(u_n)` from `C^∞(Ω) ∩ W^{1,p}(Ω)` with `u_n → u` in `W^{1,p}(Ω)`: the elements `w n` of
`W^{1,p}(Ω)` whose functions are the `u_n` converge to `u`. (The remark's second claim, that
for a general `Ω` no sequence of `C_c^1(ℝ^N)` functions need converge to `u` in `W^{1,p}(Ω)`, is
a counterexample and is not formalized.) -/
theorem remark_9_5 (hp' : p ≠ ⊤) (u : sobolevSpace N p Ω) :
    ∃ v : ℕ → 𝔼 → ℝ, (∀ n, ContDiffOn ℝ ∞ (v n) Ω) ∧
      ∃ w : ℕ → sobolevSpace N p Ω,
        (∀ n, SobolevMultiIndex.fn (w n) =ᵐ[volume.restrict (Ω : Set 𝔼)] v n) ∧
        Tendsto w atTop (𝓝 u) := by
  have hf : MemSobolev (SobolevMultiIndex.fn u) 1 p Ω volume :=
    (SobolevMultiIndex.memSobolevMultiIndex u).memSobolev
  obtain ⟨v, hvs, hvm, hvt⟩ := hf.exists_seq_contDiffOn_tendsto_sobolevNorm Fact.out hp'
  choose w hw using fun n ↦
    ((hvm n).memSobolevMultiIndex (b := 𝔟)).exists_sobolevMultiIndex
  exact ⟨v, hvs, w, hw, tendsto_of_tendsto_sobolevNorm hp' hw hvt⟩


/-! ### Proposition 9.3 -/

omit [Fact (1 ≤ p)] in
/-- A function of `L^∞` is almost everywhere bounded by its `L^∞` norm. -/
theorem ae_norm_le_toReal_eLpNorm_top {G : Type*} [NormedAddCommGroup G] {μ : Measure 𝔼}
    {f : 𝔼 → G} (hf : MemLp f ⊤ μ) : ∀ᵐ x ∂μ, ‖f x‖ ≤ (eLpNorm f ⊤ μ).toReal := by
  have hne : eLpNorm f ⊤ μ ≠ ⊤ := hf.eLpNorm_ne_top
  rw [eLpNorm_exponent_top hf.aestronglyMeasurable] at hne ⊢
  filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := μ)] with x hx
  rw [← ofReal_norm] at hx
  exact (ENNReal.ofReal_le_iff_le_toReal hne).1 hx

/-- **Proposition 9.3, (i) ⇒ (ii), with the constant `C = ‖∇u‖_{L^p(Ω)}`.** For
`u ∈ W^{1,p}(Ω)`, `1 ≤ p ≤ ∞`, `q` the conjugate exponent: `|∫_Ω u ∂φ/∂x_i| ≤ ‖∇u‖_p ‖φ‖_{p'}`
for every `φ ∈ C_c^∞(Ω)` and every `i` (the book's "obvious" direction, Hölder's inequality on
the defining identity). -/
theorem proposition_9_3_i_ii {q : ℝ≥0∞} [p.HolderConjugate q] (u : sobolevSpace N p Ω)
    (φ : 𝓓(Ω, ℝ)) (i : Fin N) :
    ‖∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn u x * fderiv ℝ φ x (EuclideanSpace.single i 1)‖ₑ
      ≤ eLpNorm (gradient u) p (volume.restrict Ω) * eLpNorm φ q (volume.restrict Ω) := by
  obtain ⟨w, hw, -, -, -, heq⟩ := exists_hasWeakFDerivOn_fn_gradient u
  have h := hw.abs_integral_smul_fderiv_le (p := p) (q := q) φ (EuclideanSpace.single i 1)
  rw [heq] at h
  have h1 : ‖(EuclideanSpace.single i (1 : ℝ) : 𝔼)‖ₑ = 1 := by
    rw [← ofReal_norm]
    simp
  rw [h1, one_mul] at h
  refine le_of_eq_of_le ?_ h
  congr 1
  exact setIntegral_congr_fun Ω.isOpen.measurableSet fun x _ ↦ by rw [smul_eq_mul, mul_comm]

/-- **Proposition 9.3, (ii) ⇒ (i).** Let `u ∈ L^p(Ω)`, `1 < p ≤ ∞`, `q` the conjugate exponent
(`1 < p` is `q < ∞`). If there is a constant `C` with `|∫_Ω u ∂φ/∂x_i| ≤ C ‖φ‖_{p'}` for every
`φ ∈ C_c^∞(Ω)` and every `i`, then `u ∈ W^{1,p}(Ω)`: the proof of Proposition 8.3, the Riesz
representation theorem in `L^{p'}(Ω)` (Theorem 4.11), gives the weak derivatives. -/
theorem proposition_9_3_ii_i {q : ℝ≥0∞} [p.HolderConjugate q] (hp : 1 < p) {u : 𝔼 → ℝ}
    (hu : MemLp u p (volume.restrict Ω)) {C : ℝ}
    (h : ∀ (φ : 𝓓(Ω, ℝ)) (i : Fin N),
      ‖∫ x in (Ω : Set 𝔼), u x * fderiv ℝ φ x (EuclideanSpace.single i 1)‖ₑ
        ≤ ENNReal.ofReal C * eLpNorm φ q (volume.restrict Ω)) :
    ∃ v : sobolevSpace N p Ω, SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼)] u := by
  have hq : q ≠ ⊤ :=
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt (p := q) (q := p)).2 hp).ne
  refine (MemSobolev.of_forall_enorm_integral_smul_fderiv_basis_le hq hu 𝔟
    (C := fun _ ↦ ENNReal.ofReal C) (fun _ ↦ ENNReal.ofReal_ne_top) fun φ i ↦ ?_)
    |>.memSobolevMultiIndex.exists_sobolevMultiIndex
  rw [basisFun_toBasis_apply]
  refine le_of_eq_of_le ?_ (h φ i)
  congr 1
  exact setIntegral_congr_fun Ω.isOpen.measurableSet fun x _ ↦ by rw [smul_eq_mul, mul_comm]

/-- **The distance `dist(ω, ∂Ω)` from a set `ω` to the boundary of `Ω`**, as an extended real:
`inf_{x ∈ ω} dist(x, ∂Ω)`, which is `∞` when `∂Ω = ∅` (the case `Ω = ℝ^N`, where every
translation makes sense). -/
noncomputable def edistFrontier (V Ω : Set 𝔼) : ℝ≥0∞ :=
  ⨅ x ∈ V, Metric.infEDist x (frontier Ω)

/-- If `|h| < dist(ω, ∂Ω)` and `ω ⊆ Ω`, the segments `[x, x + h]`, `x ∈ ω`, stay in `Ω`: the
book's "`τ_h u(x) = u(x + h)` makes sense for `x ∈ ω` and `|h| < dist(ω, ∂Ω)`". A segment
leaving the open set `Ω` would meet its boundary at distance at most `|h|` from `x`. -/
theorem segment_subset_of_enorm_lt_edistFrontier {V : Set 𝔼} (hVΩ : V ⊆ Ω) {h : 𝔼}
    (hh : ‖h‖ₑ < edistFrontier V Ω) :
    ∀ x ∈ V, ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • h ∈ (Ω : Set 𝔼) := by
  intro x hx t ht
  have hseg : segment ℝ x (x + h) ⊆ (Ω : Set 𝔼) := by
    refine (convex_segment x (x + h)).isPreconnected.subset_of_closure_inter_subset Ω.isOpen
      ⟨x, left_mem_segment ℝ x (x + h), hVΩ hx⟩ fun z ⟨hzc, hzs⟩ ↦ ?_
    by_contra hzΩ
    have hzf : z ∈ frontier (Ω : Set 𝔼) :=
      ⟨hzc, fun hzi ↦ hzΩ (Ω.isOpen.interior_eq ▸ hzi)⟩
    have h1 : edistFrontier V Ω ≤ edist x z :=
      (iInf₂_le x hx).trans (Metric.infEDist_le_edist_of_mem hzf)
    have h2 : edist x z ≤ ‖h‖ₑ := by
      rw [edist_dist, ← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      have := dist_add_dist_of_mem_segment hzs
      have h3 : dist x (x + h) = ‖h‖ := by
        rw [dist_eq_norm, sub_add_cancel_left, norm_neg]
      linarith [dist_nonneg (x := z) (y := x + h)]
    exact (hh.trans_le (h1.trans h2)).false
  refine hseg ?_
  rw [segment_eq_image']
  exact ⟨t, ht, by rw [add_sub_cancel_left]⟩

/-- **Proposition 9.3, (i) ⇒ (iii), with the constant `C = ‖∇u‖_{L^p(Ω)}`.** For `u` almost
everywhere equal to the function of `v ∈ W^{1,p}(Ω)`, `1 ≤ p ≤ ∞`, every `ω ⊂⊂ Ω` and every
`h ∈ ℝ^N` with `|h| < dist(ω, ∂Ω)`: `‖τ_h u − u‖_{L^p(ω)} ≤ ‖∇v‖_{L^p(Ω)} |h|`. -/
theorem proposition_9_3_i_iii (v : sobolevSpace N p Ω) {u : 𝔼 → ℝ}
    (hu : SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼)] u) {V : Set 𝔼}
    (hV : IsStronglyIncluded V Ω) {h : 𝔼} (hh : ‖h‖ₑ < edistFrontier V Ω) :
    eLpNorm (fun x ↦ u (x + h) - u x) p (volume.restrict V)
      ≤ eLpNorm (gradient v) p (volume.restrict Ω) * ‖h‖ₑ := by
  have hs := Ω.isOpen.measurableSet
  have hseg := segment_subset_of_enorm_lt_edistFrontier hV.subset hh
  obtain ⟨w, hw, hwp, -, -, heq⟩ := exists_hasWeakFDerivOn_fn_gradient v
  -- replace `u` by the function of `v` on `ω` and on `ω + h`
  have hu' : ∀ᵐ x ∂volume, x ∈ (Ω : Set 𝔼) → SobolevMultiIndex.fn v x = u x :=
    (ae_restrict_iff' hs).1 hu
  have hu'' : ∀ᵐ x ∂volume, x + h ∈ (Ω : Set 𝔼) → SobolevMultiIndex.fn v (x + h) = u (x + h) :=
    (measurePreserving_add_right volume h).quasiMeasurePreserving.ae hu'
  have hae : (fun x ↦ u (x + h) - u x) =ᵐ[volume.restrict V]
      fun x ↦ SobolevMultiIndex.fn v (x + h) - SobolevMultiIndex.fn v x := by
    filter_upwards [ae_restrict_mem hV.1.measurableSet, ae_restrict_of_ae hu',
      ae_restrict_of_ae hu''] with x hxV h1 h2
    have hx1 : x + h ∈ (Ω : Set 𝔼) := by simpa using hseg x hxV 1 ⟨zero_le_one, le_rfl⟩
    rw [h1 (hV.subset hxV), h2 hx1]
  rw [eLpNorm_congr_ae hae, ← heq, mul_comm]
  rcases eq_or_ne p ⊤ with rfl | hp'
  · exact hw.eLpNorm_sub_translate_le_top hV.1 h hseg
  · exact hw.eLpNorm_sub_translate_le (SobolevMultiIndex.memLp v) hwp Fact.out hp' hV.1 h hseg

/-- **Proposition 9.3, the case `Ω = ℝ^N`**: for `u ∈ W^{1,p}(ℝ^N)`, `1 ≤ p ≤ ∞`, and every
`h ∈ ℝ^N`, `‖τ_h u − u‖_{L^p(ℝ^N)} ≤ |h| ‖∇u‖_{L^p(ℝ^N)}`. -/
theorem proposition_9_3_univ (u : sobolevSpace N p ⊤) (h : 𝔼) :
    eLpNorm (fun x ↦ SobolevMultiIndex.fn u (x + h) - SobolevMultiIndex.fn u x) p volume
      ≤ ‖h‖ₑ * eLpNorm (gradient u) p volume := by
  obtain ⟨w, hw, hwp, -, -, heq⟩ := exists_hasWeakFDerivOn_fn_gradient u
  rw [eLpNorm_restrict_coe_top, eLpNorm_restrict_coe_top] at heq
  rw [← heq]
  rcases eq_or_ne p ⊤ with rfl | hp'
  · have := hw.eLpNorm_sub_translate_le_top isOpen_univ h fun _ _ _ _ ↦ Set.mem_univ _
    simpa [Measure.restrict_coe_top] using this
  · exact hw.eLpNorm_sub_translate_le_univ
      (by simpa [Measure.restrict_coe_top] using SobolevMultiIndex.memLp u)
      (by simpa [Measure.restrict_coe_top] using hwp) Fact.out hp' h

/-- **The distance `dist(ω, ∂Ω)` is positive for `ω ⊂⊂ Ω`**: there is `δ > 0` with
`δ ≤ dist(ω, ∂Ω)`, since the compact set `ω̄ ⊆ Ω` has a `δ`-thickening inside the open set `Ω`,
which its boundary avoids. -/
theorem exists_pos_ofReal_le_edistFrontier {V : Set 𝔼} (hV : IsStronglyIncluded V Ω) :
    ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ≤ edistFrontier V Ω := by
  obtain ⟨δ, hδ, hδΩ⟩ := hV.2.2.exists_thickening_subset_open Ω.isOpen hV.2.1
  refine ⟨δ, hδ, le_iInf₂ fun x hx ↦ Metric.le_infEDist.2 fun z hz ↦ ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  have hz' : z ∈ thickening δ (closure V) :=
    mem_thickening_iff.2 ⟨x, subset_closure hx, by rwa [dist_comm, ← edist_lt_ofReal]⟩
  refine hz.2 ?_
  rw [Ω.isOpen.interior_eq]
  exact hδΩ hz'

omit [Fact (1 ≤ p)] in
/-- **Proposition 9.3, (iii) ⇒ (ii).** Let `u ∈ L^p(Ω)`, `1 ≤ p ≤ ∞`, `q` the conjugate exponent.
If there is a constant `C` such that `‖τ_h u − u‖_{L^p(ω)} ≤ C |h|` for every `ω ⊂⊂ Ω` and every
`h ∈ ℝ^N` with `|h| < dist(ω, ∂Ω)`, then `|∫_Ω u ∂φ/∂x_i| ≤ C ‖φ‖_{p'}` for every `φ ∈ C_c^∞(Ω)`
and every `i`. The book's proof: with `supp φ ⊆ ω ⊂⊂ Ω` and `h = t e_i`, `t` small, the change of
variables `∫_Ω (τ_h u − u) φ = ∫_Ω u (φ(· − h) − φ)` and Hölder's inequality bound the difference
quotients of `φ` against `u` by `C ‖φ‖_{p'}`, and `t → 0` gives (ii) — the backbone's
`abs_integral_smul_fderiv_le_of_eLpNorm_sub_translate_le_of_norm_lt`, fed with the
positivity of `dist(ω, ∂Ω)` (`exists_pos_ofReal_le_edistFrontier`). -/
theorem proposition_9_3_iii_ii {q : ℝ≥0∞} [p.HolderConjugate q] {u : 𝔼 → ℝ}
    (hu : MemLp u p (volume.restrict Ω)) {C : ℝ}
    (h : ∀ V : Set 𝔼, IsStronglyIncluded V Ω → ∀ h : 𝔼, ‖h‖ₑ < edistFrontier V Ω →
      eLpNorm (fun x ↦ u (x + h) - u x) p (volume.restrict V) ≤ ENNReal.ofReal C * ‖h‖ₑ)
    (φ : 𝓓(Ω, ℝ)) (i : Fin N) :
    ‖∫ x in (Ω : Set 𝔼), u x * fderiv ℝ φ x (EuclideanSpace.single i 1)‖ₑ
      ≤ ENNReal.ofReal C * eLpNorm φ q (volume.restrict Ω) := by
  have key := abs_integral_smul_fderiv_le_of_eLpNorm_sub_translate_le_of_norm_lt (q := q) hu
    (C := ENNReal.ofReal C) (fun V hVo hVc hVΩ ↦ ?_) φ (EuclideanSpace.single i 1)
  · have h1 : ‖(EuclideanSpace.single i (1 : ℝ) : 𝔼)‖ₑ = 1 := by
      rw [← ofReal_norm]
      simp
    rw [h1, mul_one] at key
    refine le_of_eq_of_le ?_ key
    congr 1
    exact setIntegral_congr_fun Ω.isOpen.measurableSet fun x _ ↦ by rw [smul_eq_mul, mul_comm]
  · obtain ⟨δ, hδ, hδV⟩ := exists_pos_ofReal_le_edistFrontier ⟨hVo, hVΩ, hVc⟩
    refine ⟨δ, hδ, fun a ha ↦ h V ⟨hVo, hVΩ, hVc⟩ a ?_⟩
    calc ‖a‖ₑ < ENNReal.ofReal δ := by rwa [← ofReal_norm, ENNReal.ofReal_lt_ofReal_iff hδ]
      _ ≤ edistFrontier V Ω := hδV

/-- **Proposition 9.3.** Let `u ∈ L^p(Ω)` with `1 < p ≤ ∞` (`q` the conjugate exponent). The
following properties are equivalent: (i) `u ∈ W^{1,p}(Ω)`, that is, `u` is almost everywhere on
`Ω` the function of an element of `W^{1,p}(Ω)`; (ii) there is a constant `C` such that
`|∫_Ω u ∂φ/∂x_i| ≤ C ‖φ‖_{L^{p'}(Ω)}` for all `φ ∈ C_c^∞(Ω)` and all `i = 1, …, N`; (iii) there
is a constant `C` such that for all `ω ⊂⊂ Ω` and all `h ∈ ℝ^N` with `|h| < dist(ω, ∂Ω)`,
`‖τ_h u − u‖_{L^p(ω)} ≤ C |h|`. "Furthermore, we can take `C = ‖∇u‖_{L^p(Ω)}` in (ii) and (iii)"
is `proposition_9_3_i_ii` and `proposition_9_3_i_iii`, and the case `Ω = ℝ^N` is
`proposition_9_3_univ`. -/
theorem proposition_9_3 {q : ℝ≥0∞} [p.HolderConjugate q] (hp : 1 < p) {u : 𝔼 → ℝ}
    (hu : MemLp u p (volume.restrict Ω)) :
    [∃ v : sobolevSpace N p Ω, SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼)] u,
      ∃ C : ℝ, ∀ (φ : 𝓓(Ω, ℝ)) (i : Fin N),
        ‖∫ x in (Ω : Set 𝔼), u x * fderiv ℝ φ x (EuclideanSpace.single i 1)‖ₑ
          ≤ ENNReal.ofReal C * eLpNorm φ q (volume.restrict Ω),
      ∃ C : ℝ, ∀ V : Set 𝔼, IsStronglyIncluded V Ω → ∀ h : 𝔼, ‖h‖ₑ < edistFrontier V Ω →
        eLpNorm (fun x ↦ u (x + h) - u x) p (volume.restrict V)
          ≤ ENNReal.ofReal C * ‖h‖ₑ].TFAE := by
  tfae_have 1 → 2 := by
    rintro ⟨v, hv⟩
    refine ⟨(eLpNorm (gradient v) p (volume.restrict Ω)).toReal, fun φ i ↦ ?_⟩
    rw [ENNReal.ofReal_toReal (memLp_gradient v).eLpNorm_ne_top]
    refine le_of_eq_of_le ?_ (proposition_9_3_i_ii v φ i)
    congr 1
    exact integral_congr_ae (hv.symm.mono fun x hx ↦ by simp only [hx])
  tfae_have 2 → 1 := fun ⟨C, hC⟩ ↦ proposition_9_3_ii_i hp hu hC
  tfae_have 1 → 3 := by
    rintro ⟨v, hv⟩
    refine ⟨(eLpNorm (gradient v) p (volume.restrict Ω)).toReal, fun V hV h hh ↦ ?_⟩
    rw [ENNReal.ofReal_toReal (memLp_gradient v).eLpNorm_ne_top]
    exact proposition_9_3_i_iii v hv hV hh
  tfae_have 3 → 2 := fun ⟨C, hC⟩ ↦ ⟨C, proposition_9_3_iii_ii hu hC⟩
  tfae_finish

omit [Fact (1 ≤ p)] in
/-- **Remark 6.** When `p = 1` the implications (i) ⇒ (ii) ⇔ (iii) of Proposition 9.3 remain
true: for `u ∈ L^1(Ω)` (with `p' = ∞`), (i) ⇒ (ii), (i) ⇒ (iii) and (iii) ⇒ (ii), the three
backbone implications being valid for every `1 ≤ p ≤ ∞`. The implication (ii) ⇒ (iii) at
`p = 1` — that a function of bounded variation satisfies the translation estimate — belongs to
the theory of `BV` functions and is not formalized; the remark's discussion of `BV` has no node. -/
theorem remark_9_6 {u : 𝔼 → ℝ} (hu : MemLp u 1 (volume.restrict Ω)) :
    ((∃ v : sobolevSpace N 1 Ω, SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼)] u) →
      ∃ C : ℝ, ∀ (φ : 𝓓(Ω, ℝ)) (i : Fin N),
        ‖∫ x in (Ω : Set 𝔼), u x * fderiv ℝ φ x (EuclideanSpace.single i 1)‖ₑ
          ≤ ENNReal.ofReal C * eLpNorm φ ⊤ (volume.restrict Ω)) ∧
    ((∃ v : sobolevSpace N 1 Ω, SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼)] u) →
      ∃ C : ℝ, ∀ V : Set 𝔼, IsStronglyIncluded V Ω → ∀ h : 𝔼, ‖h‖ₑ < edistFrontier V Ω →
        eLpNorm (fun x ↦ u (x + h) - u x) 1 (volume.restrict V) ≤ ENNReal.ofReal C * ‖h‖ₑ) ∧
    ((∃ C : ℝ, ∀ V : Set 𝔼, IsStronglyIncluded V Ω → ∀ h : 𝔼, ‖h‖ₑ < edistFrontier V Ω →
        eLpNorm (fun x ↦ u (x + h) - u x) 1 (volume.restrict V) ≤ ENNReal.ofReal C * ‖h‖ₑ) →
      ∃ C : ℝ, ∀ (φ : 𝓓(Ω, ℝ)) (i : Fin N),
        ‖∫ x in (Ω : Set 𝔼), u x * fderiv ℝ φ x (EuclideanSpace.single i 1)‖ₑ
          ≤ ENNReal.ofReal C * eLpNorm φ ⊤ (volume.restrict Ω)) := by
  refine ⟨fun ⟨v, hv⟩ ↦ ⟨(eLpNorm (gradient v) 1 (volume.restrict Ω)).toReal, fun φ i ↦ ?_⟩,
    fun ⟨v, hv⟩ ↦ ⟨(eLpNorm (gradient v) 1 (volume.restrict Ω)).toReal, fun V hV h hh ↦ ?_⟩,
    fun ⟨C, hC⟩ ↦ ⟨C, proposition_9_3_iii_ii hu hC⟩⟩
  · rw [ENNReal.ofReal_toReal (memLp_gradient v).eLpNorm_ne_top]
    refine le_of_eq_of_le ?_ (proposition_9_3_i_ii v φ i)
    congr 1
    exact integral_congr_ae (hv.symm.mono fun x hx ↦ by simp only [hx])
  · rw [ENNReal.ofReal_toReal (memLp_gradient v).eLpNorm_ne_top]
    exact proposition_9_3_i_iii v hv hV hh

/-! ### Remark 7 -/

/-- **Remark 7, first sentence.** Every `u ∈ W^{1,∞}(Ω)` has a continuous representative on
`Ω`. -/
theorem remark_9_7 (u : sobolevSpace N ⊤ Ω) :
    ∃ ũ : 𝔼 → ℝ, ContinuousOn ũ Ω ∧ SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ := by
  obtain ⟨w, hw, hwp, -, -, heq⟩ := exists_hasWeakFDerivOn_fn_gradient u
  obtain ⟨ũ, hũ, hu, -⟩ := hw.exists_continuousOn_ae_eq_of_ae_norm_le ENNReal.toReal_nonneg
    (ae_norm_le_toReal_eLpNorm_top hwp)
  exact ⟨ũ, hũ, hu⟩

/-- **Remark 7, the convex case.** If `Ω` is convex, the continuous representative `ũ` of
`u ∈ W^{1,∞}(Ω)` satisfies `|ũ(x) − ũ(y)| ≤ ‖∇u‖_{L^∞(Ω)} |x − y|` for all `x, y ∈ Ω` (for a
convex `Ω` the geodesic distance of the book is `|x − y|`). -/
theorem remark_9_7_convex (hΩ : Convex ℝ (Ω : Set 𝔼)) (u : sobolevSpace N ⊤ Ω) :
    ∃ ũ : 𝔼 → ℝ, SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ ∧
      ∀ x ∈ (Ω : Set 𝔼), ∀ y ∈ (Ω : Set 𝔼),
        |ũ x - ũ y| ≤ (eLpNorm (gradient u) ⊤ (volume.restrict Ω)).toReal * ‖x - y‖ := by
  obtain ⟨w, hw, hwp, -, -, heq⟩ := exists_hasWeakFDerivOn_fn_gradient u
  obtain ⟨ũ, hu, hlip⟩ := hw.exists_lipschitzOnWith_ae_eq_of_convex hΩ ENNReal.toReal_nonneg
    (ae_norm_le_toReal_eLpNorm_top hwp)
  refine ⟨ũ, hu, fun x hx y hy ↦ ?_⟩
  have := hlip.dist_le_mul x hx y hy
  rwa [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ ENNReal.toReal_nonneg, heq] at this

/-- **Remark 7, last sentence.** If `u ∈ W^{1,p}(Ω)`, `1 ≤ p ≤ ∞`, and `∇u = 0` almost
everywhere on `Ω`, then `u` is (almost everywhere) constant on each connected component of
`Ω`. -/
theorem remark_9_7_const (u : sobolevSpace N p Ω)
    (h : ∀ i, partialDeriv u i =ᵐ[volume.restrict (Ω : Set 𝔼)] 0) (x₀ : 𝔼) :
    ∃ c : ℝ, SobolevMultiIndex.fn u
      =ᵐ[volume.restrict (connectedComponentIn (Ω : Set 𝔼) x₀)] fun _ ↦ c := by
  obtain ⟨w, hw, -, hwi, -, -⟩ := exists_hasWeakFDerivOn_fn_gradient u
  set Ω' : Opens 𝔼 := ⟨connectedComponentIn (Ω : Set 𝔼) x₀, Ω.isOpen.connectedComponentIn⟩
    with hΩ'
  have hle : Ω' ≤ Ω := connectedComponentIn_subset _ _
  have hw0 : w =ᵐ[volume.restrict (Ω : Set 𝔼)] 0 := by
    filter_upwards [ae_all_iff.2 fun i ↦ (hwi i).trans (h i)] with x hx
    refine ContinuousLinearMap.coe_injective ((𝔟).ext fun i ↦ ?_)
    rw [basisFun_toBasis_apply]
    simpa using hx i
  obtain ⟨c, hc⟩ := (hw.mono hle).ae_eq_const_of_isPreconnected
    (hw0.filter_mono (ae_mono (Measure.restrict_mono hle le_rfl)))
    isPreconnected_connectedComponentIn
  exact ⟨c, hc⟩

/-! ### Propositions 9.4–9.6 -/

/-- **Proposition 9.4 (differentiation of a product).** Let `u, v ∈ W^{1,p}(Ω) ∩ L^∞(Ω)`,
`1 ≤ p ≤ ∞`. Then `u v ∈ W^{1,p}(Ω) ∩ L^∞(Ω)` and `∂_i (u v) = (∂_i u) v + u (∂_i v)` for every
`i`. -/
theorem proposition_9_4 (u v : sobolevSpace N p Ω)
    (hu : MemLp (SobolevMultiIndex.fn u) ⊤ (volume.restrict Ω))
    (hv : MemLp (SobolevMultiIndex.fn v) ⊤ (volume.restrict Ω)) :
    ∃ w : sobolevSpace N p Ω,
      SobolevMultiIndex.fn w =ᵐ[volume.restrict (Ω : Set 𝔼)]
        (fun x ↦ SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x) ∧
      MemLp (SobolevMultiIndex.fn w) ⊤ (volume.restrict Ω) ∧
      ∀ i, partialDeriv w i =ᵐ[volume.restrict (Ω : Set 𝔼)] fun x ↦
        partialDeriv u i x * SobolevMultiIndex.fn v x
          + SobolevMultiIndex.fn u x * partialDeriv v i x := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  set M : ℝ := max (eLpNorm (SobolevMultiIndex.fn u) ⊤ (volume.restrict Ω)).toReal
    (eLpNorm (SobolevMultiIndex.fn v) ⊤ (volume.restrict Ω)).toReal with hM
  have hMu : ∀ᵐ x ∂volume.restrict (Ω : Set 𝔼), ‖SobolevMultiIndex.fn u x‖ ≤ M :=
    (ae_norm_le_toReal_eLpNorm_top hu).mono fun x hx ↦ hx.trans (le_max_left _ _)
  have hMv : ∀ᵐ x ∂volume.restrict (Ω : Set 𝔼), ‖SobolevMultiIndex.fn v x‖ ≤ M :=
    (ae_norm_le_toReal_eLpNorm_top hv).mono fun x hx ↦ hx.trans (le_max_right _ _)
  obtain ⟨hmem, hbound⟩ := (SobolevMultiIndex.memSobolevMultiIndex u).mul_of_ae_norm_le hp
    (SobolevMultiIndex.memSobolevMultiIndex v) hMu hMv
  have hg : ∀ i, HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1]
      (fun x ↦ SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x)
      (fun x ↦ partialDeriv u i x * SobolevMultiIndex.fn v x
        + SobolevMultiIndex.fn u x * partialDeriv v i x) Ω volume := fun i ↦
    (hasWeakIteratedLineDerivOn_partialDeriv u i).mul_of_ae_norm_le
      (hasWeakIteratedLineDerivOn_partialDeriv v i) hMu hMv
  obtain ⟨w, hw, hwi⟩ := exists_sobolevSpace_of_hasWeakIteratedLineDerivOn hmem.memLp hg
    fun i ↦ memLp_of_memSobolevMultiIndex_of_hasWeakIteratedLineDerivOn hmem (hg i)
  refine ⟨w, hw, ?_, hwi⟩
  exact (memLp_top_of_bound hmem.memLp.aestronglyMeasurable (M * M) hbound).ae_eq hw.symm

/-- **Proposition 9.5 (differentiation of a composition).** Let `G ∈ C^1(ℝ)` with `G(0) = 0`
and `|G'(s)| ≤ M` for all `s`, and let `u ∈ W^{1,p}(Ω)`, `1 ≤ p ≤ ∞`. Then `G ∘ u ∈ W^{1,p}(Ω)`
and `∂_i (G ∘ u) = (G' ∘ u) ∂_i u` for every `i`. -/
theorem proposition_9_5 {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) (hG0 : G 0 = 0) {M : ℝ}
    (hM : ∀ s, |deriv G s| ≤ M) (u : sobolevSpace N p Ω) :
    ∃ w : sobolevSpace N p Ω,
      SobolevMultiIndex.fn w =ᵐ[volume.restrict (Ω : Set 𝔼)]
        (fun x ↦ G (SobolevMultiIndex.fn u x)) ∧
      ∀ i, partialDeriv w i =ᵐ[volume.restrict (Ω : Set 𝔼)] fun x ↦
        deriv G (SobolevMultiIndex.fn u x) * partialDeriv u i x := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hmem := (SobolevMultiIndex.memSobolevMultiIndex u).contDiff_comp hp hG hG0 hM
  have hg : ∀ i, HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1]
      (fun x ↦ G (SobolevMultiIndex.fn u x))
      (fun x ↦ deriv G (SobolevMultiIndex.fn u x) * partialDeriv u i x) Ω volume := fun i ↦
    (hasWeakIteratedLineDerivOn_partialDeriv u i).contDiff_comp' hG hM
  exact exists_sobolevSpace_of_hasWeakIteratedLineDerivOn hmem.memLp hg
    fun i ↦ memLp_of_memSobolevMultiIndex_of_hasWeakIteratedLineDerivOn hmem (hg i)

/-- **Proposition 9.6 (change of variables formula).** Let `Ω, Ω' ⊆ ℝ^N` be open and let
`H : Ω' → Ω` be a bijection, `x = H(y)`, with `H ∈ C^1(Ω')`, `H⁻¹ ∈ C^1(Ω)`,
`Jac H ∈ L^∞(Ω')`, `Jac H⁻¹ ∈ L^∞(Ω)` (the backbone's `IsDiffeoOnWithBoundedJacobian`, with
footnote 6's Jacobian matrices as the derivatives `fderiv ℝ H y`), and let `u ∈ W^{1,p}(Ω)`,
`1 ≤ p ≤ ∞`. Then `u ∘ H ∈ W^{1,p}(Ω')` and
`∂_j (u ∘ H)(y) = ∑_i (∂_i u)(H y) ∂_j H_i(y)` for every `j`, where
`∂_j H_i (y) = (fderiv ℝ H y e_j) i`. -/
theorem proposition_9_6 {H Hinv : 𝔼 → 𝔼} {Ω' : Opens 𝔼} {M : ℝ}
    (hH : IsDiffeoOnWithBoundedJacobian H Hinv Ω' Ω M) (u : sobolevSpace N p Ω) :
    ∃ w : sobolevSpace N p Ω',
      SobolevMultiIndex.fn w =ᵐ[volume.restrict (Ω' : Set 𝔼)]
        (fun y ↦ SobolevMultiIndex.fn u (H y)) ∧
      ∀ j, partialDeriv w j =ᵐ[volume.restrict (Ω' : Set 𝔼)] fun y ↦
        ∑ i, partialDeriv u i (H y) * fderiv ℝ H y (EuclideanSpace.single j 1) i := by
  obtain ⟨w, hw, -, hwi, -, -⟩ := exists_hasWeakFDerivOn_fn_gradient u
  refine ⟨SobolevEuclidean.compDiffeoL hH u, SobolevMultiIndex.fn_compDiffeoL hH u, fun j ↦ ?_⟩
  -- the tensor gradient evaluated at any vector is the sum over the components
  have hall : ∀ᵐ z ∂volume.restrict (Ω : Set 𝔼), ∀ ξ : 𝔼,
      w z ξ = ∑ i, partialDeriv u i z * ξ i := by
    filter_upwards [ae_all_iff.2 hwi] with z hz ξ
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin N) ℝ).sum_repr ξ]
    simp only [map_sum, map_smul, EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr,
      smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hz i, mul_comm]
  have h1 := SobolevMultiIndex.weakDeriv_compDiffeo_single hH u hw j
  rw [basisFun_toBasis_apply] at h1
  filter_upwards [h1, hH.ae_comp_restrict hall] with y hy hy'
  rw [SobolevMultiIndex.compDiffeoL_apply] at *
  exact hy.trans (hy' _)

/-! ### The spaces `W^{m,p}(Ω)` -/

/-- **The space `W^{m,p}(Ω)`** of the paragraph "The spaces `W^{m,p}(Ω)`": the functions
`u ∈ L^p(Ω)` all of whose weak derivatives `D^α u`, `|α| ≤ m`, lie in `L^p(Ω)`
(`sobolevSpaceHigher_iff`, the book's second, multi-index definition), equivalently, by
induction, `u ∈ W^{m−1,p}(Ω)` with `∂_i u ∈ W^{m−1,p}(Ω)` for all `i`
(`sobolevSpaceHigher_iff_inductive`), as the backbone type `SobolevEuclidean N m p Ω`. -/
noncomputable abbrev sobolevSpaceHigher (N m : ℕ) (p : ℝ≥0∞)
    (Ω : Opens (EuclideanSpace ℝ (Fin N))) : Type :=
  SobolevEuclidean N m p Ω

omit [Fact (1 ≤ p)] in
/-- `W^{1,p}(Ω)` is the case `m = 1` of `W^{m,p}(Ω)`. -/
theorem sobolevSpaceHigher_one : sobolevSpaceHigher N 1 p Ω = sobolevSpace N p Ω :=
  rfl

/-- A function is (almost everywhere on `Ω`) the function of an element of `W^{m,p}(Ω)` if and
only if it satisfies the backbone's predicate `MemSobolevMultiIndex`. -/
theorem exists_fn_ae_eq_iff {m : ℕ} (u : 𝔼 → ℝ) :
    (∃ v : sobolevSpaceHigher N m p Ω, SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼)] u)
      ↔ MemSobolevMultiIndex 𝔟 u m p Ω volume :=
  ⟨fun ⟨v, hv⟩ ↦ (SobolevMultiIndex.memSobolevMultiIndex v).congr_ae hv,
    fun h ↦ h.exists_sobolevMultiIndex⟩

/-- **The multi-index definition of `W^{m,p}(Ω)`**: a function `u : ℝ^N → ℝ` is (almost
everywhere on `Ω`) the function of an element of `W^{m,p}(Ω)` if and only if `u ∈ L^p(Ω)` and,
for every multi-index `α` with `|α| ≤ m`, there is `g_α ∈ L^p(Ω)` with
`∫_Ω u D^α φ = (−1)^{|α|} ∫_Ω g_α φ` for every `φ ∈ C_c^∞(Ω)`, where `D^α φ` is the iterated
derivative of `φ` along the `|α|` directions `e_i` repeated `α_i` times
(`multiIndexTuple`). -/
theorem sobolevSpaceHigher_iff {m : ℕ} (u : 𝔼 → ℝ) :
    (∃ v : sobolevSpaceHigher N m p Ω, SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼)] u)
      ↔ MemLp u p (volume.restrict Ω) ∧ ∀ α : MultiIndexLE (Fin N) m,
        ∃ g : 𝔼 → ℝ, MemLp g p (volume.restrict Ω) ∧ ∀ φ : 𝓓(Ω, ℝ),
          ∫ x in (Ω : Set 𝔼), u x * iteratedFDeriv ℝ (∑ i, α.1 i) φ x (multiIndexTuple 𝔟 α.1)
            = (-1) ^ (∑ i, α.1 i) * ∫ x in (Ω : Set 𝔼), g x * φ x := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  rw [exists_fn_ae_eq_iff]
  constructor
  · rintro ⟨hu, h⟩
    refine ⟨hu, fun α ↦ ?_⟩
    obtain ⟨g, hg, hgp⟩ := h α.1 α.2
    exact ⟨g, hgp, integral_mul_iteratedFDeriv_eq_of_hasWeakIteratedLineDerivOn hg⟩
  · rintro ⟨hu, h⟩
    refine ⟨hu, fun α hα ↦ ?_⟩
    obtain ⟨g, hgp, hg⟩ := h ⟨α, hα⟩
    exact ⟨g, hasWeakIteratedLineDerivOn_of_forall (hu.locallyIntegrableOn hp)
      (hgp.locallyIntegrableOn hp) hg, hgp⟩

/-- **The inductive definition of `W^{m+1,p}(Ω)`**: a function `u` is in `W^{m+1,p}(Ω)` if and
only if it is in `W^{m,p}(Ω)` and, for every `i`, its weak partial derivative `∂u/∂x_i` exists
and is in `W^{m,p}(Ω)` — the book's `W^{m,p} = {u ∈ W^{m−1,p} : ∂_i u ∈ W^{m−1,p} ∀ i}`. -/
theorem sobolevSpaceHigher_iff_inductive {m : ℕ} (u : 𝔼 → ℝ) :
    (∃ v : sobolevSpaceHigher N (m + 1) p Ω,
        SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼)] u) ↔
      (∃ v : sobolevSpaceHigher N m p Ω,
        SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼)] u) ∧
      ∀ i, ∃ g : 𝔼 → ℝ, HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1] u g Ω volume ∧
        ∃ v' : sobolevSpaceHigher N m p Ω,
          SobolevMultiIndex.fn v' =ᵐ[volume.restrict (Ω : Set 𝔼)] g := by
  simp only [exists_fn_ae_eq_iff]
  rw [memSobolevMultiIndex_succ_iff]
  simp only [basisFun_toBasis_apply]

/-- **The norm of `W^{m,p}(Ω)`** the book displays, `‖u‖_{W^{m,p}} = ∑_{|α| ≤ m} ‖D^α u‖_p`;
equivalent to the norm of the type (`bookNormHigher_equiv`). -/
noncomputable def bookNormHigher {m : ℕ} (u : sobolevSpaceHigher N m p Ω) : ℝ :=
  ∑ α, ‖SobolevMultiIndex.weakDeriv u α‖

/-- **The two norms of `W^{m,p}(Ω)` are equivalent**: `‖u‖ ≤ ‖u‖_{W^{m,p}} ≤ K ‖u‖`, `K` the
number of multi-indices of order `≤ m`. -/
theorem bookNormHigher_equiv {m : ℕ} (u : sobolevSpaceHigher N m p Ω) :
    ‖u‖ ≤ bookNormHigher u ∧
      bookNormHigher u ≤ Fintype.card (MultiIndexLE (Fin N) m) * ‖u‖ := by
  refine ⟨SobolevMultiIndex.norm_le_sum_norm_weakDeriv u, ?_⟩
  calc bookNormHigher u ≤ ∑ _α : MultiIndexLE (Fin N) m, ‖u‖ :=
        Finset.sum_le_sum fun α _ ↦ SobolevMultiIndex.norm_weakDeriv_le u α
    _ = Fintype.card (MultiIndexLE (Fin N) m) * ‖u‖ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **"The space `W^{m,p}(Ω)` equipped with the norm `∑_{|α| ≤ m} ‖D^α u‖_p` is a Banach
space"**: `W^{m,p}(Ω)` is complete, and the book's norm is equivalent to the norm of the
type. -/
theorem sobolevSpaceHigher_banach {m : ℕ} :
    CompleteSpace (sobolevSpaceHigher N m p Ω) ∧
      ∀ u : sobolevSpaceHigher N m p Ω, ‖u‖ ≤ bookNormHigher u ∧
        bookNormHigher u ≤ Fintype.card (MultiIndexLE (Fin N) m) * ‖u‖ :=
  ⟨inferInstance, bookNormHigher_equiv⟩

/-- **"The space `H^m(Ω) = W^{m,2}(Ω)` equipped with the scalar product
`(u, v)_{H^m} = ∑_{|α| ≤ m} (D^α u, D^α v)_{L^2}` is a Hilbert space"**: the inner product of
the type is the book's, and the space is complete. -/
theorem hSpaceHigher {m : ℕ} :
    (∀ u v : sobolevSpaceHigher N m 2 Ω, inner ℝ u v = ∑ α, ∫ x in (Ω : Set 𝔼),
      SobolevMultiIndex.weakDeriv u α x * SobolevMultiIndex.weakDeriv v α x) ∧
    CompleteSpace (sobolevSpaceHigher N m 2 Ω) := by
  refine ⟨fun u v ↦ ?_, inferInstance⟩
  rw [SobolevMultiIndex.inner_eq, integral_finsetSum _ fun α _ ↦ L2.integrable_inner (𝕜 := ℝ)
    (SobolevMultiIndex.weakDeriv u α) (SobolevMultiIndex.weakDeriv v α)]
  simp only [Real.inner_apply]

end Brezis.Chapter09
