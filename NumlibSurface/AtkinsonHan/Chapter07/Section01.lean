import Numlib.Analysis.Sobolev.WeakDeriv

/-!
# Atkinson–Han §7.1: weak derivatives

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §7.1.

The section extends the classical derivative to the *weak* derivative on an open `Ω ⊆ ℝ^d`, by
turning the integration by parts formula (7.1.1) into a definition (Definition 7.1.3). Here `Ω` is
a `TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))` and the measure is `volume`; the backbone
predicate `HasWeakIteratedFDerivOn` works over any finite-dimensional real normed space with an
additive Haar measure.

A multi-index `α` with `|α| = n` is represented by a tuple `y : Fin n → ℝ^d` of directions, so that
`∂^α φ x` is `iteratedFDeriv ℝ n φ x y`; the backbone bundles all the multi-indices of a given
length into a single `ContinuousMultilinearMap`-valued derivative, and quantifying over all tuples
is quantifying over all `α` of that length. Test functions are Mathlib's bundled `𝓓(Ω, ℝ)`.

Definitions 7.1.1 and 7.1.3, Lemmas 7.1.2, 7.1.4 and 7.1.5 and Proposition 7.1.10 are here.
Examples 7.1.6, 7.1.7 and 7.1.8 (one-dimensional computations), Example 7.1.9 (which needs the
trace of §7.3), and Propositions 7.1.11 and 7.1.12 (the product and chain rules, which the book
states without proof and whose proofs mollify and pass to the limit) are not.
-/

open MeasureTheory TopologicalSpace

open scoped ContDiff Distributions ENNReal

namespace AtkinsonHan.Chapter07

variable {d n m : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin d))}
  {u v : EuclideanSpace ℝ (Fin d) → ℝ}

/-- **Definition 7.1.1**: for `1 ≤ p < ∞` a function `v : Ω ⊆ ℝ^d → ℝ` is locally `p`-integrable,
`v ∈ L^p_loc(Ω)`, when every point of `Ω` has a neighbourhood in `Ω` on which `v` is
`p`-integrable. The book asks for an open `Ω'` with `closure Ω' ⊆ Ω` and `v ∈ L^p(Ω')`; on an open
`Ω` that is the same condition, because every point of `Ω` has a ball whose closure is still
inside `Ω`. -/
def definition_7_1_1 (p : ℝ≥0∞) (Ω : Opens (EuclideanSpace ℝ (Fin d)))
    (v : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  LocallyMemLpOn v p Ω volume

/-- **Lemma 7.1.2** (generalized variational lemma): if `v ∈ L^1_loc(Ω)` on a nonempty open
`Ω ⊆ ℝ^d` and `∫_Ω v φ = 0` for every `φ ∈ C_0^∞(Ω)`, then `v = 0` a.e. on `Ω`. The book quotes
this from the literature without proof; it is Mathlib's
`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`. -/
theorem lemma_7_1_2 (hv : LocallyIntegrableOn v Ω volume)
    (h : ∀ φ : 𝓓(Ω, ℝ), ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin d))), v x * φ x = 0) :
    ∀ᵐ x, x ∈ (Ω : Set (EuclideanSpace ℝ (Fin d))) → v x = 0 := by
  refine Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hv fun g hg h'g hgs ↦ ?_
  have e : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin d))), v x * g x = ∫ x, g x • v x :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [show g x = 0 from image_eq_zero_of_notMem_tsupport fun hh ↦ hx (hgs hh),
        mul_zero]).trans (by simp [smul_eq_mul, mul_comm])
  exact e ▸ h ⟨g, hg, h'g, hgs⟩

/-- **Definition 7.1.3**: for `Ω ⊆ ℝ^d` nonempty open and `v, w ∈ L^1_loc(Ω)`, `w` is a weak
`α`-th derivative of `v` when `∫_Ω v ∂^α φ = (-1)^{|α|} ∫_Ω w φ` for every `φ ∈ C_0^∞(Ω)`,
which is (7.1.2). All the multi-indices of length `n` are carried by one object: `w x` is a
continuous `n`-linear map, its value at a tuple `y` of directions being the weak `∂^α v` for the
multi-index `α` that `y` names. -/
def definition_7_1_3 (n : ℕ) (v : EuclideanSpace ℝ (Fin d) → ℝ)
    (w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) [×n]→L[ℝ] ℝ)
    (Ω : Opens (EuclideanSpace ℝ (Fin d))) : Prop :=
  HasWeakIteratedFDerivOn n v w Ω volume

/-- **Lemma 7.1.4**: a weak derivative, if it exists, is uniquely defined up to a set of measure
zero. -/
theorem lemma_7_1_4 {w₁ w₂ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) [×n]→L[ℝ] ℝ}
    (h₁ : definition_7_1_3 n v w₁ Ω) (h₂ : definition_7_1_3 n v w₂ Ω) :
    ∀ᵐ x, x ∈ (Ω : Set (EuclideanSpace ℝ (Fin d))) → w₁ x = w₂ x :=
  h₁.ae_eq h₂

/-- **Lemma 7.1.5**: if `v ∈ C^m(Ω)` then for each `α` with `|α| ≤ m` the classical partial
derivative `∂^α v` is also the weak `α`-th derivative of `v`. So the weak derivative extends the
classical one, and it is natural to use the same notation for both. -/
theorem lemma_7_1_5 (hv : ContDiffOn ℝ m v Ω) (hnm : n ≤ m) :
    definition_7_1_3 n v (iteratedFDeriv ℝ n v) Ω :=
  hv.hasWeakIteratedFDerivOn (by exact_mod_cast hnm)

/-- **Proposition 7.1.10**: weak differentiation is linear. If `∂^α u` and `∂^α v` exist then so
does `∂^α (c₁ u + c₂ v)`, and it is `c₁ ∂^α u + c₂ ∂^α v`. -/
theorem proposition_7_1_10 {w₁ w₂ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) [×n]→L[ℝ] ℝ}
    (h₁ : definition_7_1_3 n u w₁ Ω) (h₂ : definition_7_1_3 n v w₂ Ω) (c₁ c₂ : ℝ) :
    definition_7_1_3 n (c₁ • u + c₂ • v) (c₁ • w₁ + c₂ • w₂) Ω :=
  h₁.const_smul_add_const_smul h₂ c₁ c₂

end AtkinsonHan.Chapter07
