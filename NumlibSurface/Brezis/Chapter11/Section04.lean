import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.MeasureTheory.Function.L2Space
import Numlib.Analysis.Convex.Duality.Conjugate
import Numlib.Analysis.Convex.Indicator
import Numlib.Analysis.InnerProductSpace.CompactSpectral.Normal
import Numlib.Analysis.Normed.Algebra.SpectralRadius
import Numlib.Analysis.Normed.Algebra.Spectrum
import Numlib.Analysis.Normed.Lp.Sequence
import Numlib.Analysis.Normed.Module.Annihilator
import Numlib.Analysis.Normed.Operator.Unbounded.Adjoint
import Numlib.Variational.Forms
import NumlibSurface.Brezis.Chapter01.Section03
import NumlibSurface.Brezis.Chapter01.Section04
import NumlibSurface.Brezis.Chapter05.Section01
import NumlibSurface.Brezis.Chapter05.Section03
import NumlibSurface.Brezis.Chapter11.Section02

/-!
# Brezis §11.4: Banach spaces over `ℂ` — what is similar and what is different

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §11.4. Here and only here the surface works over `ℂ`:
`E` is a complex normed (Banach where the book says so) space, `H` a complex Hilbert space, and
the book's `E_ℝ`, `H_ℝ` are the same types read through Mathlib's instances
`NormedSpace.complexToReal` and `InnerProductSpace.complexToReal` (the real inner product
`⟪u, v⟫_ℝ = re ⟪u, v⟫_ℂ`, `real_inner_eq_re_inner`).

Conventions. The book's inner product `(u, v)` is linear in `u`, Mathlib's `⟪u, v⟫` in `v`, so
the book's `(u, v)` is `⟪v, u⟫ = conj ⟪u, v⟫`; in particular the book's `(T u, u)` is `⟪u, T u⟫`
(the backbone's numerical range), and a form `a(u, v)` linear in `u` and conjugate-linear in `v`
is `a v u` for `a : SesqForm ℂ H` (conjugate-linear in the first slot). The map `I : f ↦ Re f`
of Proposition 11.22 is `reDual E`, Mathlib's `StrongDual.extendRCLikeₗᵢ` inverted, and it is
how the real results of chapters 1 and 5 are read over `ℂ`: the closed real hyperplanes and
separation of the geometric Hahn–Banach theorem, the conjugate `conjugateC` against the real
pairing `rePairing E : ⟨x, f⟩ = Re ⟨f, x⟩`, Stampacchia through chapter 5's Theorem 5.6 on
`H_ℝ`. The spectral theory of Propositions 11.30–11.37 is Mathlib's complex Banach-algebra
and C⋆-algebra theory of `E →L[ℂ] E` and `H →L[ℂ] H` together with the backbone
`Numlib/Analysis/Normed/Algebra/Spectrum` (numerical range, isometries, the eigenvalue spectral
mapping theorem) and `Numlib/Analysis/InnerProductSpace/CompactSpectral/Normal` (compact
normal operators, Remark 2).

## Main results

* `reDual`, `proposition_11_22`, `proposition_11_23` — `f ↦ Re f` is a bijective isometry
  `E* ≃ E_ℝ*`; Hahn–Banach over `ℂ`.
* `IsClosedRealHyperplane`, `SeparatesRe`, `proposition_11_24` — the geometric Hahn–Banach
  theorem with closed real hyperplanes; `orthogonal_complex` — `M^⊥` over `ℂ`.
* `rePairing`, `conjugateC`, `conjugateC_eq`, `biconjugateC`, `proposition_11_25`,
  `conjugateC_indicator` — the conjugate `φ*(f) = sup (Re ⟨f, x⟩ − φ(x))`, Fenchel–Moreau
  over `ℂ`, and the conjugate of an indicator.
* `inner_identities`, `inner_L2_complex`, `proposition_11_26`, `proposition_11_27`,
  `proposition_11_28`, `proposition_11_28_symm`, `laxMilgram_complex`,
  `laxMilgram_complex_bijective`, `proposition_11_29`, `remark_11_1` — chapter 5 over `ℂ`.
* `spectrum_eq_setOf_not_bijective`, `rightShift`, `example_rightShift`, `proposition_11_30`,
  `example_shift_two`, `spectralRadius_eq_lim`, `proposition_11_31`, `proposition_11_32` —
  spectrum, eigenvalues, spectral radius and the spectral mapping theorem.
* `numericalRange_eq`, `proposition_11_33`, `adjoint_smul_conj`,
  `selfAdjoint_spectrum_subset_real`, `proposition_11_34`, `isStarNormal_iff`,
  `proposition_11_35`, `proposition_11_36`, `remark_11_2`, `unitary_iff_isometry_surjective`,
  `proposition_11_37`, `skewAdjoint_iff`, `skewAdjoint_spectrum_subset_imaginary`,
  `hasDerivAt_norm_sq` — the numerical range, adjoints, normal operators, isometries.

Not formalized: the prose comparisons ("Chapter 2. All the statements are unchanged…"), the
finite-dimensional motivation, the computation `W(T) = {|λ| ≤ 1/2}` for `T(u₁, u₂) = (u₂, 0)`,
and the non-compact half of Remark 2.
-/

open Filter Metric Module.End Topology
open scoped ComplexConjugate InnerProductSpace

noncomputable section

namespace Brezis.Chapter11

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-! ### Chapter 1 over `ℂ`: the real dual, Hahn–Banach, conjugate functions -/

/-- **The map `I` of Proposition 11.22**, `f ↦ Re f`, from the complex dual `E*` to the real
dual `E_ℝ*`, as a real-linear isometric isomorphism: Mathlib's `StrongDual.extendRCLikeₗᵢ`
(whose forward direction is the book's formula (12)) inverted. -/
def reDual (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] :
    StrongDual ℂ E ≃ₗᵢ[ℝ] StrongDual ℝ E :=
  (StrongDual.extendRCLikeₗᵢ (𝕜 := ℂ) (F := E)).symm

/-- `I f = Re f`. -/
@[simp]
theorem reDual_apply (f : StrongDual ℂ E) (x : E) : reDual E f x = (f x).re :=
  rfl

/-- **Display (12).** The inverse of `I` sends `φ ∈ E_ℝ*` to `f(x) = φ(x) − i φ(i x)`. -/
theorem reDual_symm_apply (φ : StrongDual ℝ E) (x : E) :
    (reDual E).symm φ x = φ x - Complex.I * φ (Complex.I • x) :=
  rfl

/-- **Proposition 11.22.** The map `I : f ∈ E* ↦ Re f ∈ E_ℝ*` is a bijective isometry from `E*`
onto `E_ℝ*`. -/
theorem proposition_11_22 :
    ∃ I : StrongDual ℂ E ≃ₗᵢ[ℝ] StrongDual ℝ E, ∀ (f : StrongDual ℂ E) (x : E), I f x = (f x).re :=
  ⟨reDual E, fun _ _ => rfl⟩

/-- **Proposition 11.23 (Hahn–Banach over `ℂ`).** Let `G ⊆ E` be a linear subspace. If
`g : G → ℂ` is a continuous linear functional, there exists `f ∈ E*` extending `g` with
`‖f‖_{E*} = ‖g‖_{G*}`. (Mathlib's `exists_extension_norm_eq` over `RCLike`, proved as the book
proves it: Corollary 1.2 on `E_ℝ` and Proposition 11.22.) -/
theorem proposition_11_23 (G : Submodule ℂ E) (g : StrongDual ℂ G) :
    ∃ f : StrongDual ℂ E, (∀ x : G, f x = g x) ∧ ‖f‖ = ‖g‖ :=
  exists_extension_norm_eq G g

/-- **Definition.** A closed real hyperplane `H` in `E` is a set of the form
`H = {x ∈ E ; Re ⟨f, x⟩ = α} = [Re f = α]` for some `f ∈ E*`, `f ≠ 0`, and some `α ∈ ℝ`. (For
`α = 0` it is a linear subspace of `E_ℝ` but not of `E`.) -/
def IsClosedRealHyperplane (H : Set E) : Prop :=
  ∃ (f : StrongDual ℂ E) (α : ℝ), f ≠ 0 ∧ H = {x | (f x).re = α}

/-- A closed real hyperplane of `E` is exactly a closed hyperplane `[φ = α]` of `E_ℝ` in the
sense of chapter 1 (`Chapter01.IsHyperplane`, with `φ` continuous by Proposition 1.5), the
functionals corresponding through Proposition 11.22. -/
theorem isClosedRealHyperplane_iff (H : Set E) :
    IsClosedRealHyperplane H ↔ Chapter01.IsHyperplane H ∧ IsClosed H := by
  constructor
  · rintro ⟨f, α, hf, rfl⟩
    refine ⟨⟨(reDual E f : E →ₗ[ℝ] ℝ), α, fun h => hf ?_, rfl⟩, ?_⟩
    · apply (reDual E).injective
      exact ContinuousLinearMap.coe_injective (by simpa using h)
    · exact isClosed_singleton.preimage (reDual E f).continuous
  · rintro ⟨⟨g, α, hg, rfl⟩, hcl⟩
    have hcont : Continuous g := (Chapter01.proposition_1_5 g hg α).1 hcl
    refine ⟨(reDual E).symm ⟨g, hcont⟩, α, fun h => hg ?_, ?_⟩
    · have := congrArg (reDual E) h
      rw [LinearIsometryEquiv.apply_symm_apply, map_zero] at this
      exact LinearMap.ext fun x => congrArg (fun φ : StrongDual ℝ E => φ x) this
    · ext x
      simp only [Set.mem_ofPred_eq, ← reDual_apply, LinearIsometryEquiv.apply_symm_apply]
      rfl

/-- **Definition.** The hyperplane `[Re f = α]` separates `A, B ⊆ E` if `Re ⟨f, x⟩ ≤ α` for all
`x ∈ A` and `Re ⟨f, x⟩ ≥ α` for all `x ∈ B`. -/
def SeparatesRe (f : StrongDual ℂ E) (α : ℝ) (A B : Set E) : Prop :=
  (∀ x ∈ A, (f x).re ≤ α) ∧ ∀ x ∈ B, α ≤ (f x).re

/-- Separation by `[Re f = α]` is chapter 1's separation by `[I f = α]` in `E_ℝ`. -/
theorem separatesRe_iff (f : StrongDual ℂ E) (α : ℝ) (A B : Set E) :
    SeparatesRe f α A B ↔ Chapter01.Separates (reDual E f : E →ₗ[ℝ] ℝ) α A B :=
  Iff.rfl

/-- **Proposition 11.24 (geometric Hahn–Banach over `ℂ`).** Let `A, B ⊆ E` be two nonempty
disjoint convex sets, one of which is open. Then there exists a closed real hyperplane
`[Re f = α]` that separates `A` and `B`. (Theorem 1.6 on `E_ℝ`, then Proposition 11.22.) -/
theorem proposition_11_24 {A B : Set E} (hA : Convex ℝ A) (hAne : A.Nonempty) (hB : Convex ℝ B)
    (hBne : B.Nonempty) (hAB : Disjoint A B) (hopen : IsOpen A ∨ IsOpen B) :
    ∃ (f : StrongDual ℂ E) (α : ℝ), f ≠ 0 ∧ SeparatesRe f α A B := by
  obtain ⟨g, α, hg, hcl, hsep⟩ := Chapter01.theorem_1_6 hA hAne hB hBne hAB hopen
  have hcont : Continuous g := (Chapter01.proposition_1_5 g hg α).1 hcl
  refine ⟨(reDual E).symm ⟨g, hcont⟩, α, fun h => hg ?_, ?_⟩
  · have := congrArg (reDual E) h
    rw [LinearIsometryEquiv.apply_symm_apply, map_zero] at this
    exact LinearMap.ext fun x => congrArg (fun φ : StrongDual ℝ E => φ x) this
  · rw [separatesRe_iff, LinearIsometryEquiv.apply_symm_apply]
    exact hsep

/-- **The orthogonal over `ℂ`.** "The definition of the orthogonal `M^⊥` of a linear subspace
`M` of `E` is unchanged, `M^⊥ = {f ∈ E* ; ⟨f, x⟩ = 0 ∀ x ∈ M}`, and clearly
`M^⊥ = {f ∈ E* ; Re ⟨f, x⟩ = 0 ∀ x ∈ M}` (take `i x` in place of `x`). It is easily seen that
`M^⊥⊥ = M̄`." Three clauses, `M^⊥` being `M.strongDualAnnihilator` as in chapter 1. -/
theorem orthogonal_complex (M : Submodule ℂ E) :
    (∀ f : StrongDual ℂ E, f ∈ M.strongDualAnnihilator ↔ ∀ x ∈ M, f x = 0) ∧
      (∀ f : StrongDual ℂ E, f ∈ M.strongDualAnnihilator ↔ ∀ x ∈ M, (f x).re = 0) ∧
      M.strongDualAnnihilator.strongDualCoannihilator = M.topologicalClosure := by
  refine ⟨fun f => Submodule.mem_strongDualAnnihilator, fun f => ?_,
    M.strongDualCoannihilator_strongDualAnnihilator⟩
  rw [Submodule.mem_strongDualAnnihilator]
  refine ⟨fun h x hx => by rw [h x hx, Complex.zero_re], fun h x hx => ?_⟩
  have him := h (Complex.I • x) (M.smul_mem _ hx)
  rw [map_smul, smul_eq_mul, Complex.I_mul_re, neg_eq_zero] at him
  exact Complex.ext (h x hx) him

/-- **The real pairing of `E` with its complex dual**, `⟨x, f⟩ = Re ⟨f, x⟩`: chapter 1's pairing
of `E_ℝ` with `E_ℝ*` composed with `I` of Proposition 11.22. It is the pairing against which
the conjugate of a function on a complex space is taken. -/
def rePairing (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] :
    E →ₗ[ℝ] StrongDual ℂ E →ₗ[ℝ] ℝ :=
  (topDualPairing ℝ E).flip.compl₂ (reDual E).toLinearEquiv.toLinearMap

/-- `rePairing E x f = Re ⟨f, x⟩`. -/
@[simp]
theorem rePairing_apply (x : E) (f : StrongDual ℂ E) : rePairing E x f = (f x).re :=
  rfl

/-- **Definition.** Given `φ : E → (−∞, +∞]`, its conjugate `φ*` on `E*` is
`φ*(f) = sup_{x ∈ E} {Re ⟨f, x⟩ − φ(x)}`: the backbone's `ConvexAnalysis.convexConj` against
`rePairing E`, with `φ : E → EReal` as in chapter 1. -/
def conjugateC (φ : E → EReal) : StrongDual ℂ E → EReal :=
  ConvexAnalysis.convexConj (rePairing E) φ

/-- `φ*(f) = ⨆ x, Re ⟨f, x⟩ − φ(x)`. -/
theorem conjugateC_apply (φ : E → EReal) (f : StrongDual ℂ E) :
    conjugateC φ f = ⨆ x : E, (((f x).re : ℝ) : EReal) - φ x :=
  rfl

/-- "With obvious notation we have `φ*(f) = φ_ℝ*(I f)` for all `f ∈ E*`": the conjugate over
`ℂ` is the real conjugate (chapter 1's, against the pairing `(topDualPairing ℝ E).flip` of
`E_ℝ` with `E_ℝ*`) evaluated at `I f`. -/
theorem conjugateC_eq (φ : E → EReal) (f : StrongDual ℂ E) :
    conjugateC φ f = ConvexAnalysis.convexConj (topDualPairing ℝ E).flip φ (reDual E f) :=
  rfl

/-- **The biconjugate over `ℂ`**, back on `E`: `φ**(x) = sup_{f ∈ E*} {Re ⟨f, x⟩ − φ*(f)}`,
the backbone's `ConvexAnalysis.convexBiconj` against `rePairing E`. -/
def biconjugateC (φ : E → EReal) : E → EReal :=
  ConvexAnalysis.convexBiconj (rePairing E) φ

/-- `φ**(x) = ⨆ f, Re ⟨f, x⟩ − φ*(f)`. -/
theorem biconjugateC_apply (φ : E → EReal) (x : E) :
    biconjugateC φ x = ⨆ f : StrongDual ℂ E, (((f x).re : ℝ) : EReal) - conjugateC φ f :=
  rfl

/-- **The conjugate of an indicator.** "If `M` is a linear subspace of `E` and `φ = I_M`, then
`φ*(f) = sup_{x ∈ M} Re ⟨f, x⟩ = I_{M^⊥}`": on `M^⊥` the supremum is `0`; off it some `x₀ ∈ M`
has `⟨f, x₀⟩ ≠ 0`, and `x₁ = conj ⟨f, x₀⟩ • x₀ ∈ M` has `Re ⟨f, x₁⟩ = |⟨f, x₀⟩|² > 0` (the
book rotates `x₀` by `i` or `−1` instead), so `λ x₁`, `λ → ∞`, makes the supremum `+∞`. -/
theorem conjugateC_indicator (M : Submodule ℂ E) :
    conjugateC (ConvexAnalysis.indicatorFn (M : Set E)) =
      ConvexAnalysis.indicatorFn (M.strongDualAnnihilator : Set (StrongDual ℂ E)) := by
  funext f
  rw [conjugateC_apply]
  by_cases hf : f ∈ M.strongDualAnnihilator
  · rw [ConvexAnalysis.indicatorFn_of_mem hf]
    refine le_antisymm (iSup_le fun x => ?_) (le_iSup_of_le (0 : E) ?_)
    · by_cases hx : x ∈ M
      · rw [ConvexAnalysis.indicatorFn_of_mem hx, Submodule.mem_strongDualAnnihilator.1 hf x hx]
        simp
      · rw [ConvexAnalysis.indicatorFn_of_notMem hx, EReal.sub_top]
        exact bot_le
    · rw [ConvexAnalysis.indicatorFn_of_mem M.zero_mem]
      simp
  · rw [ConvexAnalysis.indicatorFn_of_notMem hf]
    obtain ⟨x₀, hx₀, hfx₀⟩ : ∃ x ∈ M, f x ≠ 0 := by
      by_contra h
      push Not at h
      exact hf (Submodule.mem_strongDualAnnihilator.2 h)
    -- a vector of `M` on which `Re f` is positive
    set x₁ : E := conj (f x₀) • x₀ with hx₁
    have hx₁M : x₁ ∈ M := M.smul_mem _ hx₀
    have hpos : 0 < (f x₁).re := by
      rw [hx₁, map_smul, smul_eq_mul, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
      positivity
    rw [iSup_eq_top]
    intro b hb
    induction b with
    | bot =>
      refine ⟨x₁, ?_⟩
      rw [ConvexAnalysis.indicatorFn_of_mem hx₁M, sub_zero]
      exact EReal.bot_lt_coe _
    | coe r =>
      -- scale `x₁` so that `Re f` exceeds `r`
      set t : ℝ := (|r| + 1) / (f x₁).re with ht
      refine ⟨(t : ℂ) • x₁, ?_⟩
      rw [ConvexAnalysis.indicatorFn_of_mem (M.smul_mem _ hx₁M), sub_zero, map_smul, smul_eq_mul,
        Complex.re_ofReal_mul, ht, div_mul_cancel₀ _ hpos.ne', EReal.coe_lt_coe_iff]
      linarith [le_abs_self r]
    | top => exact absurd hb (lt_irrefl _)

/-- **Proposition 11.25 (Fenchel–Moreau over `ℂ`).** Assume that `φ : E → (−∞, +∞]` is convex,
l.s.c. and `φ ≢ +∞`. Then `φ** = φ`. The book's first method: chapter 1's Theorem 1.11 on
`E_ℝ` together with Proposition 11.22 — `φ*(f) = φ_ℝ*(I f)` (`conjugateC_eq`), so `φ**(x)` is
the real biconjugate's supremum reindexed along the bijection `I = reDual E`. -/
theorem proposition_11_25 {φ : E → EReal} (hφ : ConvexAnalysis.ConvexFn φ)
    (hl : LowerSemicontinuous φ) (hbot : ∀ x, φ x ≠ ⊥)
    (hdom : (ConvexAnalysis.convexDom φ).Nonempty) : biconjugateC φ = φ := by
  funext x
  refine Eq.trans ?_ (congrFun (Chapter01.theorem_1_11 hφ hl hbot hdom) x)
  rw [biconjugateC_apply, Chapter01.biconjugate_apply]
  exact (reDual E).toEquiv.iSup_comp
    (g := fun g : StrongDual ℝ E => ((g x : ℝ) : EReal) - Chapter01.conjugate φ g)

/-! ### Chapter 5 over `ℂ`: complex Hilbert spaces -/

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

-- the book's `H_ℝ`: the real Hilbert space structure `Re ⟪u, v⟫` on `H`
attribute [local instance] InnerProductSpace.complexToReal

/-- **The identities of the "Chapter 5" paragraph**, in Mathlib's convention (the book's `(u, v)`
is `⟪v, u⟫`): `⟪λ u, μ v⟫ = λ̄ μ ⟪u, v⟫`; `|u + v|² = |u|² + 2 Re (u, v) + |v|²` (the book's
display has `|v|²` for `|u|²`); the Cauchy–Schwarz inequality `|(u, v)| ≤ |u| |v|`; and `H_ℝ`
with the scalar product `Re (u, v)` is a real Hilbert space, `⟪u, v⟫_ℝ = Re ⟪u, v⟫_ℂ`
(Mathlib's `InnerProductSpace.complexToReal`). -/
theorem inner_identities (u v : H) (l m : ℂ) :
    ⟪l • u, m • v⟫_ℂ = conj l * m * ⟪u, v⟫_ℂ ∧
      ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + 2 * (⟪u, v⟫_ℂ).re + ‖v‖ ^ 2 ∧
      ‖⟪u, v⟫_ℂ‖ ≤ ‖u‖ * ‖v‖ ∧ ⟪u, v⟫_ℝ = (⟪u, v⟫_ℂ).re :=
  ⟨by rw [inner_smul_left, inner_smul_right, mul_assoc], norm_add_sq (𝕜 := ℂ) u v,
    norm_inner_le_norm u v, rfl⟩

/-- **The typical example.** `L²(Ω; ℂ)` with the scalar product `(u, v) = ∫ u v̄ dμ`: in
Mathlib's convention, `⟪v, u⟫ = ∫ u(x) conj (v(x)) dμ` for `u, v ∈ L²(μ; ℂ)`. -/
theorem inner_L2_complex {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    (u v : MeasureTheory.Lp ℂ 2 μ) : ⟪v, u⟫_ℂ = ∫ x, u x * conj (v x) ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  simp only [RCLike.inner_apply]

/-- **Proposition 11.26 (projection onto a closed convex set over `ℂ`).** Let `K ⊆ H` be a
nonempty closed convex set. Then for every `f ∈ H` there exists a unique `u ∈ K` such that
`|f − u| = min_{v ∈ K} |f − v| = dist (f, K)` (`IsBestApprox K f u`, chapter 5's vocabulary:
`u ∈ K` and `|f − u| ≤ |f − v|` for all `v ∈ K`; it is `|f − u| = dist (f, K)` for `u ∈ K`).
Moreover `u` is characterized by `u ∈ K` and `Re (f − u, v − u) ≤ 0` for all `v ∈ K`. Theorem
5.2 on `H_ℝ`, where `⟪·, ·⟫_ℝ = Re ⟪·, ·⟫_ℂ`. -/
theorem proposition_11_26 [CompleteSpace H] {K : Set H} (hne : K.Nonempty) (hcl : IsClosed K)
    (hK : Convex ℝ K) (f : H) :
    (∃! u, IsBestApprox K f u) ∧
      (∀ u, IsBestApprox K f u ↔ u ∈ K ∧ ‖f - u‖ = infDist f K) ∧
      ∀ u, IsBestApprox K f u ↔ u ∈ K ∧ ∀ v ∈ K, (⟪f - u, v - u⟫_ℂ).re ≤ 0 :=
  ⟨Chapter05.theorem_5_2 hne hcl hK f,
    fun _ => ⟨fun h => ⟨h.1, (Chapter05.theorem_5_2_infDist h.1).1 h⟩,
      fun h => (Chapter05.theorem_5_2_infDist h.1).2 h.2⟩,
    fun _ => ⟨fun h => ⟨h.1, (Chapter05.theorem_5_2_iff hK h.1).1 h⟩,
      fun h => (Chapter05.theorem_5_2_iff hK h.1).2 h.2⟩⟩

/-- **Proposition 11.27 (Riesz–Fréchet over `ℂ`).** Given any `φ ∈ H*` there exists a unique
`f ∈ H` such that `φ(u) = (u, f)` for all `u ∈ H` — in Mathlib's convention `φ u = ⟪f, u⟫` —
and `|f| = ‖φ‖_{H*}`. Mathlib's `InnerProductSpace.toDual`, stated over `RCLike`. -/
theorem proposition_11_27 [CompleteSpace H] (φ : StrongDual ℂ H) :
    (∃! f : H, ∀ u, φ u = ⟪f, u⟫_ℂ) ∧ ∀ f : H, (∀ u, φ u = ⟪f, u⟫_ℂ) → ‖f‖ = ‖φ‖ := by
  have hrep : ∀ f : H, (∀ u, φ u = ⟪f, u⟫_ℂ) → InnerProductSpace.toDual ℂ H f = φ :=
    fun f hf => ContinuousLinearMap.ext fun u => by
      rw [InnerProductSpace.toDual_apply_apply, hf u]
  refine ⟨⟨(InnerProductSpace.toDual ℂ H).symm φ, fun u => ?_, fun f hf => ?_⟩, fun f hf => ?_⟩
  · rw [InnerProductSpace.toDual_symm_apply]
  · rw [← hrep f hf, LinearIsometryEquiv.symm_apply_apply]
  · rw [← hrep f hf, LinearIsometryEquiv.norm_map]

/-- The real bilinear form `(u, v) ↦ Re a(u, v)` on `H_ℝ` of a form `a` satisfying (13) — in
Mathlib's convention `a : SesqForm ℂ H`, the book's `a(u, v)` being `a v u`. -/
private def reBilin (a : SesqForm ℂ H) : Chapter05.BilinForm H :=
  LinearMap.mk₂ ℝ (fun u v => (a v u).re)
    (fun u₁ u₂ v => by rw [map_add, Complex.add_re])
    (fun c u v => by
      rw [← Complex.coe_smul, map_smul, smul_eq_mul, Complex.re_ofReal_mul, smul_eq_mul])
    (fun u v₁ v₂ => by rw [map_add, add_apply, Complex.add_re])
    (fun c u v => by
      rw [← Complex.coe_smul, map_smulₛₗ, smul_apply, smul_eq_mul, Complex.conj_ofReal,
        Complex.re_ofReal_mul, smul_eq_mul])

private theorem reBilin_apply (a : SesqForm ℂ H) (u v : H) : reBilin a u v = (a v u).re :=
  rfl

private theorem reBilin_isContinuousWith (a : SesqForm ℂ H) :
    (reBilin a).IsContinuousWith ‖a‖ := fun u v => by
  rw [reBilin_apply]
  calc |(a v u).re| ≤ ‖a v u‖ := Complex.abs_re_le_norm _
    _ ≤ ‖a‖ * ‖v‖ * ‖u‖ := a.le_opNorm₂ v u
    _ = ‖a‖ * ‖u‖ * ‖v‖ := by ring

private theorem reBilin_isCoerciveWith (a : SesqForm ℂ H) {α : ℝ} (ha : a.IsCoerciveWith α) :
    (reBilin a).IsCoerciveWith α := fun v => ha v

/-- **Proposition 11.28 (Stampacchia over `ℂ`).** Let `a : H × H → ℂ` satisfy (13) (linear in
the first argument, conjugate-linear in the second: `a v u` for `a : SesqForm ℂ H`), (14)
(continuity, built into `SesqForm`) and (15) (coercivity, `Re a(u, u) ≥ α |u|²` with `α > 0`).
Let `K` be a nonempty closed convex set in `H`. Then for every `φ ∈ H*` there exists a unique
`u ∈ K` such that `Re a(u, v − u) ≥ Re ⟨φ, v − u⟩` for all `v ∈ K` (display (16)). Proof as the
book's: Theorem 5.6 on `H_ℝ` for the real form `Re a` and the real functional `Re φ`. -/
theorem proposition_11_28 [CompleteSpace H] (a : SesqForm ℂ H) {α : ℝ} (hα : 0 < α)
    (ha : a.IsCoerciveWith α) {K : Set H} (hne : K.Nonempty) (hcl : IsClosed K)
    (hK : Convex ℝ K) (φ : StrongDual ℂ H) :
    ∃! u, u ∈ K ∧ ∀ v ∈ K, (φ (v - u)).re ≤ (a (v - u) u).re :=
  Chapter05.theorem_5_6 (reBilin_isContinuousWith a) hα (reBilin_isCoerciveWith a ha) hne hcl hK
    (reDual H φ)

/-- **Proposition 11.28, "moreover".** If `a(v, w) = conj a(w, v)` for all `v, w` (`a` is
Hermitian), then `u` is characterized by `u ∈ K` and
`½ a(u, u) − Re ⟨φ, u⟩ = min_{v ∈ K} {½ a(v, v) − Re ⟨φ, v⟩}` (`a(v, v)` is real for a Hermitian
form, so it is written `Re a(v, v)`); and that minimizer exists and is unique. -/
theorem proposition_11_28_symm [CompleteSpace H] (a : SesqForm ℂ H) {α : ℝ} (hα : 0 < α)
    (ha : a.IsCoerciveWith α) (hs : a.IsHermitian) {K : Set H} (hne : K.Nonempty)
    (hcl : IsClosed K) (hK : Convex ℝ K) (φ : StrongDual ℂ H) :
    (∀ u, (u ∈ K ∧ ∀ v ∈ K, (φ (v - u)).re ≤ (a (v - u) u).re) ↔
        (u ∈ K ∧ IsMinOn (fun v => 1 / 2 * (a v v).re - (φ v).re) K u)) ∧
      ∃! u, u ∈ K ∧ IsMinOn (fun v => 1 / 2 * (a v v).re - (φ v).re) K u := by
  have hsymm : LinearMap.BilinForm.IsSymm (reBilin a) :=
    LinearMap.BilinForm.isSymm_def.2 fun u v => by
      rw [reBilin_apply, reBilin_apply, hs v u, Complex.conj_re]
  exact Chapter05.theorem_5_6_symm (reBilin_isContinuousWith a) hα (reBilin_isCoerciveWith a ha)
    hsymm hne hcl hK (reDual H φ)

/-- **Lax–Milgram over `ℂ`.** "When `K = H`, (16) becomes `a(u, v) = conj ⟨φ, v⟩` for all
`v ∈ H`": for a coercive form `a` and `φ ∈ H*`, the solutions of (16) on `K = H` are exactly
the `u` with `a v u = conj (φ v)` for all `v` (in Mathlib's convention), and there is exactly
one of them. -/
theorem laxMilgram_complex [CompleteSpace H] (a : SesqForm ℂ H) {α : ℝ} (hα : 0 < α)
    (ha : a.IsCoerciveWith α) (φ : StrongDual ℂ H) :
    (∀ u, (∀ v, (φ (v - u)).re ≤ (a (v - u) u).re) ↔ ∀ v, a v u = conj (φ v)) ∧
      ∃! u, ∀ v, a v u = conj (φ v) := by
  have key : ∀ u, (∀ v, (φ (v - u)).re ≤ (a (v - u) u).re) ↔ ∀ v, a v u = conj (φ v) := by
    intro u
    constructor
    · intro h
      -- `v - u` ranges over all of `H`
      have h' : ∀ w, (φ w).re ≤ (a w u).re := fun w => by simpa using h (w + u)
      intro w
      have h1 : (φ w).re = (a w u).re := by
        have := h' (-w)
        rw [map_neg, map_neg, neg_apply, Complex.neg_re, Complex.neg_re,
          neg_le_neg_iff] at this
        exact le_antisymm (h' w) this
      have h2 : (φ w).im = -(a w u).im := by
        have := h' (Complex.I • w)
        rw [map_smul, map_smulₛₗ, smul_apply, smul_eq_mul, smul_eq_mul,
          Complex.I_mul_re, Complex.conj_I, neg_mul, Complex.neg_re, Complex.I_mul_re,
          neg_neg, neg_le] at this
        have := h' (-(Complex.I • w))
        rw [map_neg, map_neg, neg_apply, Complex.neg_re, Complex.neg_re,
          map_smul, map_smulₛₗ, smul_apply, smul_eq_mul, smul_eq_mul,
          Complex.I_mul_re, Complex.conj_I, neg_mul, Complex.neg_re, Complex.I_mul_re] at this
        linarith
      exact Complex.ext (by rw [Complex.conj_re, h1]) (by rw [Complex.conj_im, h2, neg_neg])
    · intro h v
      rw [h (v - u), Complex.conj_re]
  refine ⟨key, ?_⟩
  have := proposition_11_28 a hα ha Set.univ_nonempty isClosed_univ convex_univ φ
  refine (existsUnique_congr fun u => ?_).1 this
  rw [← key u]
  simp only [Set.mem_univ, true_and, true_implies]

/-- **Proposition 11.29 (Lax–Milgram, modulus form).** Assume that `T ∈ 𝓛(H)` satisfies
`|(T u, u)| ≥ α |u|²` for all `u ∈ H`, for some `α > 0` (display (18)). Then `T` is bijective.
The book's proof is Remark 8 of chapter 5 (injective with closed range by `α |u| ≤ |T u|`, dense
range since `v ⊥ R(T)` forces `α |v|² ≤ |(T v, v)| = 0`); Mathlib's
`ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map` is that argument. -/
theorem proposition_11_29 [CompleteSpace H] (T : H →L[ℂ] H) {α : ℝ} (hα : 0 < α)
    (h : ∀ u, α * ‖u‖ ^ 2 ≤ ‖⟪u, T u⟫_ℂ‖) : Function.Bijective T :=
  ContinuousLinearMap.isUnit_iff_bijective.1 <|
    ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map T (c := ⟨α, hα.le⟩) hα fun u => by
      rw [← inner_conj_symm, RCLike.norm_conj, mul_comm]
      exact h u

/-- **"In particular any operator `T ∈ 𝓛(H)` satisfying `Re (T u, u) ≥ α |u|²` for all `u`,
for some `α > 0` (display (17)), is bijective from `H` onto itself."** The book's `(T u, u)` is
`⟪u, T u⟫`. -/
theorem laxMilgram_complex_bijective [CompleteSpace H] (T : H →L[ℂ] H) {α : ℝ} (hα : 0 < α)
    (h : ∀ u, α * ‖u‖ ^ 2 ≤ (⟪u, T u⟫_ℂ).re) : Function.Bijective T :=
  proposition_11_29 T hα fun u => (h u).trans (Complex.re_le_norm _)

/-- **Remark 1.** Clearly (17) implies (18). Conversely, if (18) holds, then there exists
`ξ ∈ ℂ` with `|ξ| = 1` such that `Re (ξ T u, u) ≥ α |u|²` for all `u` (display (19)): the
numerical range `W(T)` is convex (Proposition 11.33) with `dist (0, W(T)) ≥ α`, and a rotation
brings the projection of `0` onto `closure W(T)` to the positive real axis. -/
theorem remark_11_1 (T : H →L[ℂ] H) {α : ℝ} (hα : 0 < α) :
    ((∀ u, α * ‖u‖ ^ 2 ≤ (⟪u, T u⟫_ℂ).re) → ∀ u, α * ‖u‖ ^ 2 ≤ ‖⟪u, T u⟫_ℂ‖) ∧
      ((∀ u, α * ‖u‖ ^ 2 ≤ ‖⟪u, T u⟫_ℂ‖) →
        ∃ ξ : ℂ, ‖ξ‖ = 1 ∧ ∀ u, α * ‖u‖ ^ 2 ≤ (⟪u, (ξ • T) u⟫_ℂ).re) :=
  ⟨fun h u => (h u).trans (Complex.re_le_norm _),
    fun h => T.exists_re_inner_smul_ge_of_norm_inner_ge hα h⟩

end Hilbert

/-! ### Chapter 6 over `ℂ`: resolvent set, spectrum, eigenvalues, spectral radius -/

section Banach

variable [CompleteSpace E]

/-- **The definitions of §6.3 over `ℂ`.** For `T ∈ 𝓛(E)` on a complex Banach space: the
resolvent set `ρ(T) = {λ ∈ ℂ ; T − λ I is bijective from E onto E}` is Mathlib's
`resolventSet ℂ T` (bijective and invertible in `𝓛(E)` agree by the open mapping theorem, which
is where completeness enters); the spectrum `σ(T) = ℂ ∖ ρ(T)` is `spectrum ℂ T`; `λ` is an
eigenvalue, `Module.End.HasEigenvalue T λ`, iff the eigenspace `N(T − λ I) ≠ {0}`; and clearly
`EV(T) ⊆ σ(T)`. Four clauses. -/
theorem spectrum_eq_setOf_not_bijective (T : E →L[ℂ] E) :
    resolventSet ℂ T = {l | Function.Bijective ((T - l • (1 : E →L[ℂ] E) : E →L[ℂ] E) : E → E)} ∧
      spectrum ℂ T = (resolventSet ℂ T)ᶜ ∧
      (∀ l : ℂ, Module.End.HasEigenvalue (T : Module.End ℂ E) l ↔
        LinearMap.ker ((T : E →ₗ[ℂ] E) - l • 1) ≠ ⊥) ∧
      {l | Module.End.HasEigenvalue (T : Module.End ℂ E) l} ⊆ spectrum ℂ T := by
  refine ⟨?_, rfl, fun l => ?_, fun l hl => ?_⟩
  · ext l
    rw [Set.mem_ofPred_eq, spectrum.mem_resolventSet_iff, ← IsUnit.neg_iff, neg_sub,
      Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.isUnit_iff_bijective]
  · rw [← Module.End.eigenspace_def]
    exact Iff.rfl
  · rw [ContinuousLinearMap.spectrum_eq]
    exact hl.mem_spectrum

end Banach

/-! #### The right shift on `ℓ²` -/

section RightShift

variable (𝕜 : Type*) [RCLike 𝕜]

/-- **The right shift** `T u = (0, u₁, u₂, …)` on `ℓ²(ℕ; 𝕜)`: the backbone's `lp.shiftRightL 𝕜`
(`Numlib/Analysis/Normed/Lp/Sequence`), an isometry (`norm_rightShift_apply`). -/
def rightShift : lp (fun _ : ℕ => 𝕜) 2 →L[𝕜] lp (fun _ : ℕ => 𝕜) 2 :=
  lp.shiftRightL 𝕜

/-- `(T u)₀ = 0`. -/
@[simp]
theorem rightShift_apply_zero (u : lp (fun _ : ℕ => 𝕜) 2) : rightShift 𝕜 u 0 = 0 :=
  lp.shiftRightL_apply_zero 𝕜 u

/-- `(T u)ₙ₊₁ = uₙ`. -/
@[simp]
theorem rightShift_apply_succ (u : lp (fun _ : ℕ => 𝕜) 2) (n : ℕ) :
    rightShift 𝕜 u (n + 1) = u n :=
  lp.shiftRightL_apply_succ 𝕜 u n

/-- The right shift is an isometry: `‖T u‖ = ‖u‖`. -/
theorem norm_rightShift_apply (u : lp (fun _ : ℕ => 𝕜) 2) : ‖rightShift 𝕜 u‖ = ‖u‖ :=
  lp.norm_shiftRightL_apply 𝕜 u

end RightShift

/-- **"It may happen that `EV(T) = ∅`"**: the right shift `T u = (0, u₁, u₂, …)` on `ℓ²(ℕ; ℂ)`
has no eigenvalue. If `T u = λ u` then `λ u₀ = 0` and `uₙ = λ uₙ₊₁` for all `n`; for `λ = 0`
this gives `u = 0` directly, and for `λ ≠ 0` it gives `u₀ = 0` and then `uₙ = 0` by
induction. -/
theorem example_rightShift (l : ℂ) :
    ¬ Module.End.HasEigenvalue ((rightShift ℂ : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] _) :
      Module.End ℂ (lp (fun _ : ℕ => ℂ) 2)) l := by
  intro hl
  obtain ⟨u, hu⟩ := hl.exists_hasEigenvector
  have hTu : rightShift ℂ u = l • u := hu.apply_eq_smul
  have h0 : l * u 0 = 0 := by
    have := congrArg (fun v : lp (fun _ : ℕ => ℂ) 2 => v 0) hTu
    simpa [lp.coeFn_smul] using this.symm
  have hsucc : ∀ n, u n = l * u (n + 1) := fun n => by
    have := congrArg (fun v : lp (fun _ : ℕ => ℂ) 2 => v (n + 1)) hTu
    simpa [lp.coeFn_smul] using this
  refine hu.2 (lp.ext (funext fun n => ?_))
  rw [lp.coeFn_zero, Pi.zero_apply]
  rcases eq_or_ne l 0 with rfl | hl0
  · rw [hsucc n, zero_mul]
  · have hu0 : u 0 = 0 := (mul_eq_zero.1 h0).resolve_left hl0
    induction n with
    | zero => exact hu0
    | succ n ih =>
      have := hsucc n
      rw [ih] at this
      exact (mul_eq_zero.1 this.symm).resolve_left hl0

section Banach

variable [CompleteSpace E]

/-- **Proposition 11.30.** For `T ∈ 𝓛(E)` on a (nontrivial) complex Banach space, the spectrum
`σ(T)` is a nonempty compact set and `σ(T) ⊆ {λ ∈ ℂ ; |λ| ≤ ‖T‖}`. Nonemptiness is Liouville's
theorem (Mathlib's `spectrum.nonempty`, which the book does not prove). -/
theorem proposition_11_30 [Nontrivial E] (T : E →L[ℂ] E) :
    (spectrum ℂ T).Nonempty ∧ IsCompact (spectrum ℂ T) ∧ spectrum ℂ T ⊆ closedBall 0 ‖T‖ :=
  ⟨spectrum.nonempty T, spectrum.isCompact T, spectrum.subset_closedBall_norm T⟩

end Banach

/-- **"The estimate `|λ| ≤ ‖T‖` is usually not sharp"**: in `ℂ²` the operator
`T(u₁, u₂) = (u₂, 0)` satisfies `σ(T) = {0}` and `‖T‖ = 1` — `T² = 0`, so `σ(T) ⊆ {0}` by the
spectral mapping theorem, and `σ(T) ≠ ∅`; `‖T u‖ = |u₂| ≤ ‖u‖` with equality at `u = (0, 1)`. -/
theorem example_shift_two :
    ∃ T : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2),
      (∀ u, T u 0 = u 1 ∧ T u 1 = 0) ∧ spectrum ℂ T = {0} ∧ ‖T‖ = 1 := by
  set e₀ : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single 0 1 with he₀
  set T : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
    (EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 2)).smulRight e₀ with hT
  have hTapply : ∀ u, T u = u 1 • e₀ := fun u => rfl
  have hTu : ∀ u : EuclideanSpace ℂ (Fin 2), T u 0 = u 1 ∧ T u 1 = 0 := fun u => by
    rw [hTapply, he₀]
    simp
  refine ⟨T, hTu, ?_, ?_⟩
  · -- `T ^ 2 = 0`
    have hsq : T ^ 2 = 0 := by
      ext u i
      rw [sq, mul_apply_eq_comp, hTapply (T u), (hTu u).2, zero_smul]
      simp
    have hsub : spectrum ℂ T ⊆ {0} := by
      intro l hl
      have hmem : l ^ 2 ∈ spectrum ℂ (T ^ 2) := by
        rw [spectrum.map_pow]
        exact ⟨l, hl, rfl⟩
      rw [hsq, spectrum.zero_eq] at hmem
      exact pow_eq_zero_iff two_ne_zero |>.1 hmem
    exact (Set.Nonempty.subset_singleton_iff (spectrum.nonempty T)).1 hsub
  · refine le_antisymm (ContinuousLinearMap.opNorm_le_bound T zero_le_one fun u => ?_) ?_
    · rw [one_mul, hTapply, norm_smul, he₀, PiLp.norm_single, norm_one, mul_one]
      exact PiLp.norm_apply_le u 1
    · have h1 : ‖T (EuclideanSpace.single 1 1)‖ = 1 := by
        rw [hTapply, he₀]
        simp
      have := T.le_opNorm (EuclideanSpace.single (1 : Fin 2) (1 : ℂ))
      rwa [h1, PiLp.norm_single, norm_one, mul_one] at this

section Banach

variable [CompleteSpace E]

/-- **The spectral radius.** "`r(T) = lim ‖Tⁿ‖^{1/n}` exists (Exercise 6.23), and clearly
`r(T) ≤ ‖T‖`." Mathlib defines `spectralRadius ℂ T` as `sup {|λ| ; λ ∈ σ(T)}` and proves the
limit formula (Gelfand), so this node together with Proposition 11.31 says that the book's
definition and Mathlib's agree. -/
theorem spectralRadius_eq_lim (T : E →L[ℂ] E) :
    Tendsto (fun n : ℕ => ‖T ^ n‖ ^ (1 / n : ℝ)) atTop (𝓝 (spectralRadius ℂ T).toReal) ∧
      (spectralRadius ℂ T).toReal ≤ ‖T‖ :=
  ⟨spectrum.pow_norm_pow_one_div_tendsto_nhds_toReal_spectralRadius T, by
    have h := ENNReal.toReal_mono ENNReal.coe_ne_top (spectralRadius_le_nnnorm (𝕜 := ℂ) T)
    rwa [ENNReal.coe_toReal, coe_nnnorm] at h⟩

/-- **Proposition 11.31.** For every `T ∈ 𝓛(E)` on a nontrivial complex Banach space,
`r(T) = max {|λ| ; λ ∈ σ(T)}`: the maximum is attained and equals the spectral radius. -/
theorem proposition_11_31 [Nontrivial E] (T : E →L[ℂ] E) :
    IsGreatest ((fun l : ℂ => ‖l‖) '' spectrum ℂ T) (spectralRadius ℂ T).toReal := by
  obtain ⟨z, hz, hzr⟩ := spectrum.exists_nnnorm_eq_spectralRadius T
  refine ⟨⟨z, hz, ?_⟩, ?_⟩
  · rw [← hzr, ENNReal.coe_toReal, coe_nnnorm]
  · rintro _ ⟨l, hl, rfl⟩
    have h : (‖l‖₊ : ENNReal) ≤ spectralRadius ℂ T := by
      rw [spectralRadius_eq_of_unital]
      exact le_iSup₂ (f := fun l (_ : l ∈ spectrum ℂ T) => (‖l‖₊ : ENNReal)) l hl
    have := ENNReal.toReal_mono (spectrum.spectralRadius_ne_top T) h
    rwa [ENNReal.coe_toReal, coe_nnnorm] at this

open Polynomial in
/-- **Proposition 11.32, display (21).** For a polynomial `Q` with complex coefficients and
`T ∈ 𝓛(E)` on a nontrivial complex Banach space, `σ(Q(T)) = Q(σ(T))` (Mathlib's
`spectrum.map_polynomial_aeval`, whose proof is the book's factorization of `Q − μ`). -/
theorem proposition_11_32_spectrum [Nontrivial E] (T : E →L[ℂ] E) (Q : ℂ[X]) :
    spectrum ℂ (aeval T Q) = (fun l => Q.eval l) '' spectrum ℂ T :=
  spectrum.map_polynomial_aeval T Q

omit [CompleteSpace E] in
open Polynomial in
/-- **Proposition 11.32, display (20).** For a polynomial `Q` of positive degree,
`EV(Q(T)) = Q(EV(T))`, the eigenvalues being those of `T` as a linear map. The degree
hypothesis is not in the book but is needed: for a constant `Q = c` and the right shift
(`example_rightShift`, `EV(T) = ∅`), `EV(Q(T)) = EV(c I) = {c}` while `Q(EV(T)) = ∅`. -/
theorem proposition_11_32_eigenvalue (T : E →L[ℂ] E) {Q : ℂ[X]} (hQ : 0 < Q.degree) :
    {μ | Module.End.HasEigenvalue (aeval (T : Module.End ℂ E) Q) μ} =
      (fun l => Q.eval l) '' {l | Module.End.HasEigenvalue (T : Module.End ℂ E) l} := by
  ext μ
  rw [Set.mem_ofPred_eq, Module.End.hasEigenvalue_aeval_iff _ hQ]
  exact ⟨fun ⟨ν, hν, h⟩ => ⟨ν, hν, h⟩, fun ⟨ν, hν, h⟩ => ⟨ν, hν, h⟩⟩

open Polynomial in
/-- **Proposition 11.32.** Both displays: `Q(EV(T)) = EV(Q(T))` (for `0 < deg Q`) and
`Q(σ(T)) = σ(Q(T))`. -/
theorem proposition_11_32 [Nontrivial E] (T : E →L[ℂ] E) {Q : ℂ[X]} (hQ : 0 < Q.degree) :
    (fun l => Q.eval l) '' {l | Module.End.HasEigenvalue (T : Module.End ℂ E) l} =
        {μ | Module.End.HasEigenvalue (aeval (T : Module.End ℂ E) Q) μ} ∧
      (fun l => Q.eval l) '' spectrum ℂ T = spectrum ℂ (aeval T Q) :=
  ⟨(proposition_11_32_eigenvalue T hQ).symm, (proposition_11_32_spectrum T Q).symm⟩

end Banach


/-! ### Hilbert spaces over `ℂ`: numerical range, adjoints, normal operators, isometries -/

section HilbertSpectrum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Definition.** The numerical range of `T ∈ 𝓛(H)` is `W(T) = {(T u, u) ; u ∈ H, |u| = 1}` —
in Mathlib's convention `⟪u, T u⟫` — and it is the backbone's `LinearMap.numericalRange`
(the set of Rayleigh quotients `⟪x, T x⟫ / ⟪x, x⟫`, `x ≠ 0`). -/
theorem numericalRange_eq (T : H →L[ℂ] H) :
    (T : H →ₗ[ℂ] H).numericalRange = {z | ∃ u : H, ‖u‖ = 1 ∧ ⟪u, T u⟫_ℂ = z} := by
  ext z
  rw [LinearMap.mem_numericalRange, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
    refine ⟨((‖x‖⁻¹ : ℝ) : ℂ) • x, ?_, ?_⟩
    · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
        inv_mul_cancel₀ hx']
    · rw [ContinuousLinearMap.coe_coe, map_smul, inner_smul_left, inner_smul_right,
        Complex.conj_ofReal, inner_self_eq_norm_sq_to_K, div_eq_inv_mul, ← mul_assoc]
      congr 1
      push_cast
      rw [sq, mul_inv]
      rfl
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u, norm_ne_zero_iff.1 (hu ▸ one_ne_zero), ?_⟩
    rw [ContinuousLinearMap.coe_coe, inner_self_eq_norm_sq_to_K, hu]
    simp

variable [CompleteSpace H]

/-- **Proposition 11.33.** (i) `σ(T) ⊆ closure W(T)`; (ii) more precisely, if
`λ ∉ closure W(T)` then `λ ∈ ρ(T)` with `‖(T − λ I)⁻¹‖ ≤ 1 / dist (λ, W(T))` — the inverse
being Mathlib's `resolvent T λ = (λ I − T)⁻¹ = −(T − λ I)⁻¹`, of the same norm; (iii) `W(T)`
is convex (Toeplitz–Hausdorff, which the book quotes from Halmos and the backbone proves). -/
theorem proposition_11_33 (T : H →L[ℂ] H) :
    spectrum ℂ T ⊆ closure (T : H →ₗ[ℂ] H).numericalRange ∧
      (∀ l ∉ closure (T : H →ₗ[ℂ] H).numericalRange, l ∈ resolventSet ℂ T ∧
        ‖resolvent T l‖ ≤ 1 / infDist l (T : H →ₗ[ℂ] H).numericalRange) ∧
      Convex ℝ (T : H →ₗ[ℂ] H).numericalRange :=
  ⟨T.spectrum_subset_closure_numericalRange, fun l hl =>
    ⟨T.mem_resolventSet_of_notMem_closure_numericalRange hl, by
      rw [one_div]
      exact T.norm_resolvent_le_inv_infDist_numericalRange hl⟩,
    LinearMap.convex_numericalRange _⟩

/-- **The "word of caution" on adjoints.** With `H*` identified with `H` (Proposition 11.27),
the adjoint `T* ∈ 𝓛(H)` is defined by `(T u, v) = (u, T* v)` — Mathlib's
`ContinuousLinearMap.adjoint`, `⟪T u, v⟫ = ⟪u, T† v⟫` — and then `(λ T)* = λ̄ T*` (display
(24)), whereas the dual-space adjoint `T* ∈ 𝓛(H*)` of chapter 2 (`strongDualMap`) satisfies
`(λ T)* = λ T*`. -/
theorem adjoint_smul_conj (T : H →L[ℂ] H) (l : ℂ) :
    (∀ u v, ⟪T u, v⟫_ℂ = ⟪u, ContinuousLinearMap.adjoint T v⟫_ℂ) ∧
      ContinuousLinearMap.adjoint (l • T) = conj l • ContinuousLinearMap.adjoint T ∧
      (l • T).strongDualMap = l • T.strongDualMap :=
  ⟨fun u v => (ContinuousLinearMap.adjoint_inner_right T u v).symm,
    LinearIsometryEquiv.map_smulₛₗ _ l T, ContinuousLinearMap.ext fun v => by
      ext u
      simp⟩

/-- **Self-adjoint operators.** "If `T` is self-adjoint (`T* = T`), then
`(T u, u) = (u, T u) = conj (T u, u)`, so `(T u, u) ∈ ℝ` for all `u`; in particular
`W(T) ⊆ ℝ` and thus `σ(T) ⊆ ℝ`." Three clauses. -/
theorem selfAdjoint_spectrum_subset_real {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) :
    (∀ u, (⟪u, T u⟫_ℂ).im = 0) ∧ (∀ z ∈ (T : H →ₗ[ℂ] H).numericalRange, z.im = 0) ∧
      ∀ l ∈ spectrum ℂ T, l.im = 0 := by
  have hre : ∀ u, (⟪u, T u⟫_ℂ).im = 0 := fun u => by
    have h := hT.isSymmetric.conj_inner_sym u u
    rw [Complex.conj_eq_iff_im] at h
    rw [← inner_conj_symm, Complex.conj_im, neg_eq_zero]
    exact h
  have hW : ∀ z ∈ (T : H →ₗ[ℂ] H).numericalRange, z.im = 0 := by
    rw [numericalRange_eq]
    rintro _ ⟨u, -, rfl⟩
    exact hre u
  refine ⟨hre, hW, fun l hl => ?_⟩
  have hcl : closure (T : H →ₗ[ℂ] H).numericalRange ⊆ {z : ℂ | z.im = 0} :=
    closure_minimal hW (isClosed_eq Complex.continuous_im continuous_const)
  exact hcl ((proposition_11_33 T).1 hl)

/-- **Proposition 11.34.** Let `H` be a complex Hilbert space and `T` a compact self-adjoint
operator. Then there exists a Hilbert basis composed of eigenvectors of `T`, and the
corresponding eigenvalues are real (the book assumes `H` separable; the Hilbert-basis form
needs no separability, the basis being indexed by a subset `w` of `H`). Chapter 6's Theorem
6.11 over `RCLike`, read at `ℂ`. -/
theorem proposition_11_34 {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) (hK : IsCompactOperator T) :
    ∃ (w : Set H) (b : HilbertBasis w ℂ H) (μ : w → ℝ),
      ⇑b = ((↑) : w → H) ∧ ∀ i, T (b i) = (μ i : ℂ) • b i :=
  ContinuousLinearMap.IsSymmetric.exists_hilbertBasis_eigenvectors hT.isSymmetric hK

/-- **Definition.** `T ∈ 𝓛(H)` is normal if `T* ∘ T = T ∘ T*`: Mathlib's `IsStarNormal T`;
and the characterization of Problem 43 "still remains valid over `ℂ`": `T` is normal iff
`|T u| = |T* u|` for all `u`. -/
theorem isStarNormal_iff (T : H →L[ℂ] H) :
    (IsStarNormal T ↔ ContinuousLinearMap.adjoint T ∘L T = T ∘L ContinuousLinearMap.adjoint T) ∧
      (IsStarNormal T ↔ ∀ u, ‖T u‖ = ‖ContinuousLinearMap.adjoint T u‖) :=
  ⟨by
    rw [_root_.isStarNormal_iff, Commute, SemiconjBy, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def],
    ContinuousLinearMap.isStarNormal_iff_norm_eq_adjoint⟩

/-- **Proposition 11.35.** Let `H` be a (nontrivial) complex Hilbert space and `T` a normal
operator. Then `max {|λ| ; λ ∈ σ(T)} = ‖T‖` (display (25)): Mathlib's
`IsStarNormal.spectralRadius_eq_nnnorm` in the C⋆-algebra `𝓛(H)` with Proposition 11.31. -/
theorem proposition_11_35 [Nontrivial H] {T : H →L[ℂ] H} (hT : IsStarNormal T) :
    IsGreatest ((fun l : ℂ => ‖l‖) '' spectrum ℂ T) ‖T‖ := by
  have := hT
  have h := proposition_11_31 T
  rwa [IsStarNormal.spectralRadius_eq_nnnorm T, ENNReal.coe_toReal, coe_nnnorm] at h

/-- **Proposition 11.36.** Let `H` be a complex Hilbert space and `T` a compact normal operator.
Then there exists a Hilbert basis composed of eigenvectors of `T` (the eigenvalues need not be
real; the book's separability is not needed). The backbone follows the book's proof: "exactly
as in the proof of Theorem 6.11", with Proposition 11.35 in place of Corollary 6.10. -/
theorem proposition_11_36 {T : H →L[ℂ] H} (hT : IsStarNormal T) (hK : IsCompactOperator T) :
    ∃ (w : Set H) (b : HilbertBasis w ℂ H),
      ⇑b = ((↑) : w → H) ∧ ∀ i : w, ∃ μ : ℂ, T i = μ • (i : H) :=
  ContinuousLinearMap.IsStarNormal.exists_hilbertBasis_eigenvector hT hK

/-- **Remark 2.** For a compact normal operator `T`, `closure W(T) = conv σ(T)` (the convex hull
of a compact subset of `ℂ` is closed, so the plain convex hull): in an eigenbasis
`(T u, u) = ∑ λᵢ |uᵢ|²` with `∑ |uᵢ|² = 1`. The remark's second sentence (every normal `T`,
Halmos) is not formalized. -/
theorem remark_11_2 {T : H →L[ℂ] H} (hT : IsStarNormal T) (hK : IsCompactOperator T) :
    closure (T : H →ₗ[ℂ] H).numericalRange = convexHull ℝ (spectrum ℂ T) :=
  ContinuousLinearMap.IsStarNormal.closure_numericalRange_eq_convexHull_spectrum hT hK

/-- **Definition.** `T ∈ 𝓛(H)` is an isometry if `|T u| = |u|` for all `u` (Mathlib's
`Isometry T`), and a unitary operator if it is an isometry that is also surjective (membership
in Mathlib's `unitary (H →L[ℂ] H)`, `T* T = T T* = I`). -/
theorem unitary_iff_isometry_surjective (T : H →L[ℂ] H) :
    (Isometry T ↔ ∀ u, ‖T u‖ = ‖u‖) ∧
      (T ∈ unitary (H →L[ℂ] H) ↔ Isometry T ∧ Function.Surjective T) := by
  refine ⟨AddMonoidHomClass.isometry_iff_norm T, fun hT => ⟨?_, fun v => ?_⟩,
    fun ⟨hi, hs⟩ => ContinuousLinearMap.mem_unitary_of_isometry_of_surjective hi hs⟩
  · rw [ContinuousLinearMap.isometry_iff_adjoint_comp_self, ← ContinuousLinearMap.mul_def,
      ← ContinuousLinearMap.star_eq_adjoint]
    exact Unitary.star_mul_self_of_mem hT
  · refine ⟨star T v, ?_⟩
    have h := Unitary.mul_star_self_of_mem hT
    rw [← mul_apply_eq_comp, h, one_apply_eq_self]

omit [CompleteSpace H] in
/-- **Proposition 11.37, first clause.** Let `T` be an isometry. Then
`EV(T) ⊆ S¹ = {λ ∈ ℂ ; |λ| = 1}`. -/
theorem proposition_11_37_eigenvalue {T : H →L[ℂ] H} (hT : Isometry T) :
    {l | Module.End.HasEigenvalue (T : Module.End ℂ H) l} ⊆ sphere (0 : ℂ) 1 := fun l hl => by
  rw [mem_sphere_zero_iff_norm]
  exact ContinuousLinearMap.norm_eq_one_of_hasEigenvalue_of_isometry hT hl

/-- **Proposition 11.37, second clause.** If `T` is a unitary operator, then `σ(T) ⊆ S¹`. -/
theorem proposition_11_37_unitary {T : H →L[ℂ] H} (hT : Isometry T)
    (hs : Function.Surjective T) : spectrum ℂ T ⊆ sphere (0 : ℂ) 1 :=
  spectrum.subset_circle_of_unitary ((unitary_iff_isometry_surjective T).2.2 ⟨hT, hs⟩)

/-- **Proposition 11.37, third clause.** If the isometry `T` is not a unitary operator (not
surjective), then `σ(T) = {λ ∈ ℂ ; |λ| ≤ 1}` (Problem 44, question 6, adapted). -/
theorem proposition_11_37_not_unitary {T : H →L[ℂ] H} (hT : Isometry T)
    (hs : T ∉ unitary (H →L[ℂ] H)) : spectrum ℂ T = closedBall (0 : ℂ) 1 :=
  ContinuousLinearMap.spectrum_eq_closedBall_of_isometry_of_not_surjective hT fun h =>
    hs ((unitary_iff_isometry_surjective T).2.2 ⟨hT, h⟩)

/-- **Proposition 11.37.** Let `T` be an isometry. Then `EV(T) ⊆ S¹`; if `T` is unitary then
`σ(T) ⊆ S¹`, and if `T` is not unitary then `σ(T) = {|λ| ≤ 1}`. -/
theorem proposition_11_37 {T : H →L[ℂ] H} (hT : Isometry T) :
    {l | Module.End.HasEigenvalue (T : Module.End ℂ H) l} ⊆ sphere (0 : ℂ) 1 ∧
      (T ∈ unitary (H →L[ℂ] H) → spectrum ℂ T ⊆ sphere (0 : ℂ) 1) ∧
      (T ∉ unitary (H →L[ℂ] H) → spectrum ℂ T = closedBall (0 : ℂ) 1) :=
  ⟨proposition_11_37_eigenvalue hT, fun hu => spectrum.subset_circle_of_unitary hu,
    proposition_11_37_not_unitary hT⟩

/-- **Skew-adjoint operators.** `T ∈ 𝓛(H)` is skew-adjoint (or antisymmetric) if `T* = −T`;
"clearly `T` is skew-adjoint if and only if `i T` is self-adjoint (this follows from (24))". -/
theorem skewAdjoint_iff (T : H →L[ℂ] H) :
    ContinuousLinearMap.adjoint T = -T ↔ IsSelfAdjoint (Complex.I • T) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff', (adjoint_smul_conj T Complex.I).2.1, Complex.conj_I,
    neg_smul]
  constructor
  · intro h
    rw [h, smul_neg, neg_neg]
  · intro h
    have := congrArg (fun S : H →L[ℂ] H => Complex.I • S) h
    simp only [smul_neg, smul_smul, Complex.I_mul_I, neg_smul, one_smul, neg_neg] at this
    rw [this]

/-- "Thus, for any skew-adjoint operator we have `EV(T) ⊆ σ(T) ⊆ closure W(T) ⊆ i ℝ`": for
`T* = −T`, `Re (T u, u) = 0` for all `u`, so the closure of `W(T)`, the spectrum and the
eigenvalues all lie on the imaginary axis. -/
theorem skewAdjoint_spectrum_subset_imaginary {T : H →L[ℂ] H}
    (hT : ContinuousLinearMap.adjoint T = -T) :
    (∀ u, (⟪u, T u⟫_ℂ).re = 0) ∧
      (∀ z ∈ closure (T : H →ₗ[ℂ] H).numericalRange, z.re = 0) ∧
      (∀ l ∈ spectrum ℂ T, l.re = 0) ∧
      ∀ l, Module.End.HasEigenvalue (T : Module.End ℂ H) l → l.re = 0 := by
  have hre : ∀ u, (⟪u, T u⟫_ℂ).re = 0 := fun u => by
    have h : ⟪T u, u⟫_ℂ = -⟪u, T u⟫_ℂ := by
      rw [← ContinuousLinearMap.adjoint_inner_right, hT, neg_apply, inner_neg_right]
    have h' : RCLike.re ⟪T u, u⟫_ℂ = RCLike.re (-⟪u, T u⟫_ℂ) := congrArg RCLike.re h
    rw [inner_re_symm, map_neg] at h'
    change RCLike.re ⟪u, T u⟫_ℂ = 0
    linarith
  have hW : ∀ z ∈ (T : H →ₗ[ℂ] H).numericalRange, z.re = 0 := by
    rw [numericalRange_eq]
    rintro _ ⟨u, -, rfl⟩
    exact hre u
  have hcl : ∀ z ∈ closure (T : H →ₗ[ℂ] H).numericalRange, z.re = 0 :=
    closure_minimal hW (isClosed_eq Complex.continuous_re continuous_const)
  refine ⟨hre, hcl, fun l hl => hcl l ((proposition_11_33 T).1 hl), fun l hl =>
    hcl l ((proposition_11_33 T).1 ((spectrum_eq_setOf_not_bijective T).2.2.2 hl))⟩

end HilbertSpectrum

/-- **The "Chapter 7" identity.** If `φ : ℝ → H` is differentiable at `t` with derivative `φ'`,
then `|φ|²` is differentiable at `t` with `d/dt |φ|² = 2 Re (dφ/dt, φ)` — in Mathlib's
convention `2 Re ⟪φ', φ t⟫` — since `(φ', φ) + (φ, φ') = (φ', φ) + conj (φ', φ)`. This is what
the computations of §7.2–7.4 use over `ℂ`; the monotonicity condition `Re (A v, v) ≥ 0` is
chapter 7's `LinearPMap.IsMonotone`, already stated with `re`. -/
theorem hasDerivAt_norm_sq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {φ : ℝ → H} {φ' : H} {t : ℝ} (h : HasDerivAt φ φ' t) :
    HasDerivAt (fun s => ‖φ s‖ ^ 2) (2 * (⟪φ', φ t⟫_ℂ).re) t := by
  let _ := InnerProductSpace.complexToReal (G := H)
  have := h.norm_sq
  rwa [real_inner_eq_re_inner (𝕜 := ℂ), inner_re_symm] at this


end Brezis.Chapter11

end
