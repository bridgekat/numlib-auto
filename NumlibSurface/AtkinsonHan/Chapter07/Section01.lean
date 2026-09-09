import Mathlib.Analysis.Calculus.Deriv.Abs
import Numlib.Analysis.Sobolev.MultiIndex

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

Definition 7.1.3 is therefore here twice. `definition_7_1_3` is the bundled reading, one object for
all the `α` of a given length; `definition_7_1_3_multiIndex` is the book's, one multi-index at a
time, `α` being read as the tuple `stdBasis` names — the coordinate direction `e_i` repeated `α i`
times. The bundled reading implies the other, `definition_7_1_3_multiIndex_of_definition_7_1_3`.
The multi-index reading is what §7.2 needs, because the norm of Definition 7.2.2 sums over the `α`
separately.

Definitions 7.1.1 and 7.1.3, Lemmas 7.1.2, 7.1.4 and 7.1.5 and Proposition 7.1.10 are here, and so
are Examples 7.1.6, 7.1.7 and 7.1.8, the one-dimensional computations, the last in both of its
halves (`example_7_1_8` and `example_7_1_8_second_order`). Those live on
`E1 = EuclideanSpace ℝ (Fin 1)`, which the linear isometry `toE1 : ℝ ≃ₗᵢ[ℝ] E1` identifies with
`ℝ`: `toE1` is measure preserving, so an integral over `Ω ⊆ ℝ^1` is an integral over
`toE1 ⁻¹' Ω ⊆ ℝ` and the whole of Definition 7.1.3 in dimension one reduces, by `transport`, to a
single identity between interval integrals. That identity is in turn a one-dimensional integration
by parts allowing finitely many exceptional points, `integralByParts`. The second half of
Example 7.1.8 goes through `secondOrder_bridge`, which reads a second-order weak derivative as a
first-order weak derivative of the first-order one, and then through the jump obstruction of
Example 7.1.7 in its general form.

Proposition 7.1.11, the product rule, is here for a *smooth* factor, as
`proposition_7_1_11_contDiff`: there `g φ` is again a test function and the identity is a direct
integration by parts. The book states it for two merely locally integrable factors, which needs
mollification in `L^p` on a domain, and that generality is not here; neither is Proposition 7.1.12,
the chain rule, which needs the same. Example 7.1.9 needs the trace of §7.3 and is not here either.
-/

open MeasureTheory Module TopologicalSpace Set intervalIntegral

open scoped ContDiff Distributions ENNReal Interval

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

/-- The standard basis `e_1, …, e_d` of `ℝ^d`, in which the multi-index derivatives
`∂^α = ∂_1^{α_1} ⋯ ∂_d^{α_d}` of this chapter are taken. -/
noncomputable abbrev stdBasis (d : ℕ) : Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) :=
  (EuclideanSpace.basisFun (Fin d) ℝ).toBasis

/-- **Definition 7.1.3**, one multi-index at a time: for `Ω ⊆ ℝ^d` nonempty open and
`v, w ∈ L^1_loc(Ω)`, `w` is the weak `α`-th derivative of `v` when
`∫_Ω v ∂^α φ = (-1)^{|α|} ∫_Ω w φ` for every `φ ∈ C_0^∞(Ω)`. The multi-index `α` is read as the
tuple of `|α| = α_1 + ⋯ + α_d` directions it names, `e_i` repeated `α i` times with the indices in
increasing order, so that `∂^α φ` is `∂_1^{α_1} ⋯ ∂_d^{α_d} φ`. `definition_7_1_3` is the same
definition for all the multi-indices of a given length at once. -/
def definition_7_1_3_multiIndex (α : Fin d → ℕ) (v w : EuclideanSpace ℝ (Fin d) → ℝ)
    (Ω : Opens (EuclideanSpace ℝ (Fin d))) : Prop :=
  HasWeakIteratedLineDerivOn (multiIndexTuple (stdBasis d) α) v w Ω volume

/-- The bundled reading of Definition 7.1.3 gives the multi-index reading: the weak derivative of
order `|α|`, evaluated at the tuple of directions naming `α`, is the weak `∂^α`. -/
theorem definition_7_1_3_multiIndex_of_definition_7_1_3 (α : Fin d → ℕ)
    {w : EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) [×(∑ i, α i)]→L[ℝ] ℝ}
    (h : definition_7_1_3 (∑ i, α i) v w Ω) :
    definition_7_1_3_multiIndex α v (fun x ↦ w x (multiIndexTuple (stdBasis d) α)) Ω :=
  h.lineDeriv _

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

/-- **Proposition 7.1.11 with one smooth factor** (the product rule): let `α` be a multi-index of
order one, so that `∂^α` is a single first-order partial derivative `∂_i`. If `∂^α u` exists
weakly on `Ω` and `g ∈ C^∞(ℝ^d)`, then `∂^α (u g)` exists weakly and equals `(∂^α u) g + u ∂^α g`,
the second `∂^α g` being the classical derivative of `g`.

The proposition as the book states it allows *both* factors to be merely locally `p`-integrable
with locally `q`-integrable weak derivatives, for conjugate `p, q ∈ (1, ∞)`; that generality is
`proposition_7_1_11` and is not proved here. What makes the smooth case elementary is that `g φ`
is again a test function when `φ` is, so the identity is a direct integration by parts,
`∫ (∂^α φ) g u = ∫ ∂^α(g φ) u - ∫ φ (∂^α g) u`. -/
theorem proposition_7_1_11_contDiff {α : Fin d → ℕ} (hα : ∑ i, α i = 1)
    {w : EuclideanSpace ℝ (Fin d) → ℝ} (h : definition_7_1_3_multiIndex α u w Ω)
    {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : ContDiff ℝ ∞ g) :
    definition_7_1_3_multiIndex α (fun x ↦ u x * g x)
      (fun x ↦ w x * g x
        + u x * iteratedFDeriv ℝ (∑ i, α i) g x (multiIndexTuple (stdBasis d) α)) Ω :=
  HasWeakIteratedLineDerivOn.mul_contDiff h hα hg

/-! ### The line `ℝ^1`

Examples 7.1.6, 7.1.7 and 7.1.8 are computations in dimension `d = 1`. They are stated on
`E1 = EuclideanSpace ℝ (Fin 1)`, the `d = 1` case of the ambient space of §7.1, and proved on `ℝ`
through the linear isometry `toE1`. -/

section OneDimensional

/-- The Euclidean line `ℝ^1`, the `d = 1` case of the ambient space of §7.1. -/
abbrev E1 : Type := EuclideanSpace ℝ (Fin 1)

variable {Ω₁ : Opens E1}

/-- The line `ℝ` as `ℝ^1`, a linear isometry sending `t` to the point with coordinate `t`. Being an
isometry of finite-dimensional real inner product spaces it preserves the volume, so an integral
over a subset of `ℝ^1` is an integral over its preimage in `ℝ`. -/
noncomputable def toE1 : ℝ ≃ₗᵢ[ℝ] E1 where
  toLinearEquiv :=
    (LinearEquiv.funUnique (Fin 1) ℝ ℝ).symm.trans (WithLp.linearEquiv 2 ℝ (Fin 1 → ℝ)).symm
  norm_map' t := by
    simp [EuclideanSpace.norm_eq, LinearEquiv.funUnique, Real.sqrt_sq_eq_abs]

@[simp] theorem toE1_apply (t : ℝ) : (toE1 t) 0 = t := rfl

@[simp] theorem toE1_symm_apply (x : E1) : toE1.symm x = x 0 := rfl

/-- `toE1 1` is the single vector of the standard basis of `ℝ^1`. -/
theorem toE1_one : toE1 1 = stdBasis 1 0 := by
  ext i; fin_cases i; simp [stdBasis]

/-- In dimension one the tuple of directions naming the multi-index `α = (k)` is the constant tuple
`toE1 1`, of length `k`: `∂^α` is the `k`-th derivative in the single coordinate direction. -/
theorem multiIndexTuple_dimOne (k : ℕ) :
    multiIndexTuple (stdBasis 1) ![k] = fun _ ↦ toE1 1 := by
  have hl : multiIndexDirections (⇑(stdBasis 1)) ![k] = List.replicate k (stdBasis 1 0) := by
    simp [multiIndexDirections]
  funext j
  simp only [multiIndexTuple]
  rw [List.get_of_eq hl]
  simp [toE1_one]

/-- Change of variables along `toE1` in a set integral. -/
theorem setIntegral_toE1 (g : E1 → ℝ) (s : Set E1) :
    ∫ t in toE1 ⁻¹' s, g (toE1 t) = ∫ x in s, g x :=
  toE1.measurePreserving.setIntegral_preimage_emb toE1.toHomeomorph.measurableEmbedding g s

/-- A point of `ℝ^1` whose coordinate vanishes is the origin. -/
theorem eq_zero_of_apply_zero {x : E1} (h : x 0 = 0) : x = 0 := by
  ext i; fin_cases i; simpa using h

/-- Almost every point of `ℝ^1` has a nonzero coordinate: the origin is a null set. -/
theorem ae_apply_ne_zero : ∀ᵐ x : E1, x 0 ≠ 0 := by
  have h : {x : E1 | ¬ (x 0 ≠ 0)} = {0} := by
    ext x
    simp only [ne_eq, not_not, mem_ofPred_eq, mem_singleton_iff]
    exact ⟨eq_zero_of_apply_zero, fun hx ↦ by rw [hx]; rfl⟩
  rw [ae_iff, h]
  simp

/-- A single real number is a null set. -/
theorem ae_ne_real (c : ℝ) : ∀ᵐ t : ℝ, t ≠ c := by
  rw [ae_iff]; simp

/-- A bounded, a.e. strongly measurable function is locally integrable. -/
private theorem locallyIntegrable_of_bound {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {μ : Measure X} [IsLocallyFiniteMeasure μ] {w : X → ℝ} {C : ℝ}
    (hm : AEStronglyMeasurable w μ) (hb : ∀ᵐ x ∂μ, ‖w x‖ ≤ C) :
    LocallyIntegrable w μ :=
  (locallyIntegrable_const C).mono hm (by
    filter_upwards [hb] with x hx using hx.trans (le_abs_self C))

/-- A bounded, a.e. strongly measurable function is interval integrable. -/
private theorem intervalIntegrable_of_bound {f : ℝ → ℝ} {C : ℝ}
    (hm : AEStronglyMeasurable f volume) (hb : ∀ᵐ t : ℝ, ‖f t‖ ≤ C) (a b : ℝ) :
    IntervalIntegrable f volume a b :=
  (intervalIntegrable_const (c := C)).mono_fun' hm.restrict (ae_restrict_of_ae hb)

/-! ### Pulling a test function on `Ω ⊆ ℝ^1` back to `ℝ` -/

/-- A test function on `Ω ⊆ ℝ^1`, read on the line, is smooth. -/
theorem contDiff_comp_toE1 (φ : 𝓓(Ω₁, ℝ)) : ContDiff ℝ ∞ ((φ : E1 → ℝ) ∘ toE1) :=
  φ.contDiff.comp toE1.toContinuousLinearEquiv.contDiff

/-- A test function on `Ω ⊆ ℝ^1`, read on the line, has compact support. -/
theorem hasCompactSupport_comp_toE1 (φ : 𝓓(Ω₁, ℝ)) :
    HasCompactSupport ((φ : E1 → ℝ) ∘ toE1) :=
  φ.hasCompactSupport.comp_homeomorph toE1.toHomeomorph

/-- A test function on `Ω ⊆ ℝ^1`, read on the line, is supported in the preimage of `Ω`. -/
theorem tsupport_comp_toE1 (φ : 𝓓(Ω₁, ℝ)) :
    tsupport ((φ : E1 → ℝ) ∘ toE1) ⊆ toE1 ⁻¹' (Ω₁ : Set E1) := by
  rw [show ((φ : E1 → ℝ) ∘ toE1) = (φ : E1 → ℝ) ∘ toE1.toHomeomorph from rfl,
    tsupport_comp_eq_preimage]
  exact preimage_mono φ.tsupport_subset

/-- The derivative on the line of a test function on `Ω ⊆ ℝ^1` is its partial derivative in the
single coordinate direction. -/
theorem deriv_comp_toE1 (φ : 𝓓(Ω₁, ℝ)) (t : ℝ) :
    deriv ((φ : E1 → ℝ) ∘ toE1) t = fderiv ℝ (φ : E1 → ℝ) (toE1 t) (toE1 1) :=
  (((φ.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt.comp t
    toE1.toContinuousLinearEquiv.hasFDerivAt).hasDerivAt).deriv

/-- An integral over `Ω ⊆ ℝ^1` against a test function, read on the line. -/
theorem integral_testFunction_mul (φ : 𝓓(Ω₁, ℝ)) (g : E1 → ℝ) :
    ∫ x in (Ω₁ : Set E1), φ x • g x ∂volume
      = ∫ t in toE1 ⁻¹' (Ω₁ : Set E1), ((φ : E1 → ℝ) ∘ toE1) t * g (toE1 t) :=
  (setIntegral_toE1 (fun x ↦ φ x • g x) _).symm

/-- An integral over `Ω ⊆ ℝ^1` against the first derivative of a test function, read on the
line. -/
theorem integral_iteratedFDeriv_mul (φ : 𝓓(Ω₁, ℝ)) (g : E1 → ℝ) :
    ∫ x in (Ω₁ : Set E1), iteratedFDeriv ℝ 1 (φ : E1 → ℝ) x (fun _ ↦ toE1 1) • g x ∂volume
      = ∫ t in toE1 ⁻¹' (Ω₁ : Set E1), deriv ((φ : E1 → ℝ) ∘ toE1) t * g (toE1 t) := by
  simp only [iteratedFDeriv_one_apply, deriv_comp_toE1]
  exact (setIntegral_toE1 (fun x ↦ fderiv ℝ (φ : E1 → ℝ) x (toE1 1) • g x) _).symm

/-- **Definition 7.1.3 in dimension one, read on the line**: `w` is the first-order weak derivative
of `v` on `Ω ⊆ ℝ^1` as soon as both are locally integrable there and the integration by parts
formula `∫ ψ' v = -∫ ψ w` holds on `toE1 ⁻¹' Ω ⊆ ℝ` for every smooth compactly supported `ψ`
supported there. -/
theorem transport {v w : E1 → ℝ}
    (hv : LocallyIntegrableOn v Ω₁ volume) (hw : LocallyIntegrableOn w Ω₁ volume)
    (key : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ toE1 ⁻¹' (Ω₁ : Set E1) →
        (∫ t in toE1 ⁻¹' (Ω₁ : Set E1), deriv ψ t * v (toE1 t))
          = -∫ t in toE1 ⁻¹' (Ω₁ : Set E1), ψ t * w (toE1 t)) :
    definition_7_1_3_multiIndex ![1] v w Ω₁ := by
  rw [definition_7_1_3_multiIndex, multiIndexTuple_dimOne]
  refine ⟨hv, hw, fun φ ↦ ?_⟩
  change ∫ x in (Ω₁ : Set E1), iteratedFDeriv ℝ 1 (φ : E1 → ℝ) x (fun _ ↦ toE1 1) • v x ∂volume
      = (-1 : ℝ) ^ 1 • ∫ x in (Ω₁ : Set E1), φ x • w x ∂volume
  rw [integral_iteratedFDeriv_mul, integral_testFunction_mul,
    key _ (contDiff_comp_toE1 φ) (hasCompactSupport_comp_toE1 φ) (tsupport_comp_toE1 φ)]
  simp

/-- The converse of `transport`: a first-order weak derivative on `Ω ⊆ ℝ^1` gives the integration
by parts formula on the line, for every smooth compactly supported function supported in
`toE1 ⁻¹' Ω`. -/
theorem transport_symm {v w : E1 → ℝ} (h : definition_7_1_3_multiIndex ![1] v w Ω₁)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcs : HasCompactSupport ψ)
    (hsupp : tsupport ψ ⊆ toE1 ⁻¹' (Ω₁ : Set E1)) :
    (∫ t in toE1 ⁻¹' (Ω₁ : Set E1), deriv ψ t * v (toE1 t))
      = -∫ t in toE1 ⁻¹' (Ω₁ : Set E1), ψ t * w (toE1 t) := by
  rw [definition_7_1_3_multiIndex, multiIndexTuple_dimOne] at h
  have hφ : ContDiff ℝ ∞ (ψ ∘ toE1.symm) :=
    hψ.comp toE1.symm.toContinuousLinearEquiv.contDiff
  have hφcs : HasCompactSupport (ψ ∘ toE1.symm) := hcs.comp_homeomorph toE1.symm.toHomeomorph
  have hφts : tsupport (ψ ∘ toE1.symm) ⊆ (Ω₁ : Set E1) := by
    rw [show (ψ ∘ toE1.symm) = ψ ∘ toE1.symm.toHomeomorph from rfl, tsupport_comp_eq_preimage]
    intro y hy
    have h2 : toE1.symm y ∈ tsupport ψ := hy
    have h3 := hsupp h2
    rwa [mem_preimage, LinearIsometryEquiv.apply_symm_apply] at h3
  set φ : 𝓓(Ω₁, ℝ) := ⟨ψ ∘ toE1.symm, hφ, hφcs, hφts⟩ with hφdef
  have hcoe : ((φ : E1 → ℝ) ∘ toE1) = ψ := by funext t; simp [hφdef]
  have key : ∫ x in (Ω₁ : Set E1),
        iteratedFDeriv ℝ 1 (φ : E1 → ℝ) x (fun _ ↦ toE1 1) • v x ∂volume
      = (-1 : ℝ) ^ 1 • ∫ x in (Ω₁ : Set E1), φ x • w x ∂volume := h.integral_smul_eq φ
  rw [integral_iteratedFDeriv_mul, integral_testFunction_mul, hcoe] at key
  simpa using key

/-- **A second-order weak derivative of `v` is a first-order weak derivative of its first-order
weak derivative.** In dimension one the multi-index `(2)` names the tuple of two copies of the
coordinate direction, and for a test function `φ` the derivative `∂^2 φ` along that tuple is
`∂(∂φ)`, `∂φ` being a test function again; so the second-order identity applied to `φ` is the
first-order identity applied to `∂φ`. -/
theorem secondOrder_bridge {v w z : E1 → ℝ}
    (hw : definition_7_1_3_multiIndex ![1] v w Ω₁)
    (hz : definition_7_1_3_multiIndex ![2] v z Ω₁) :
    definition_7_1_3_multiIndex ![1] w z Ω₁ := by
  rw [definition_7_1_3_multiIndex, multiIndexTuple_dimOne] at hw ⊢
  rw [definition_7_1_3_multiIndex, multiIndexTuple_dimOne] at hz
  refine ⟨hw.locallyIntegrableOn_weakDeriv, hz.locallyIntegrableOn_weakDeriv, fun φ ↦ ?_⟩
  have e1 : ∀ x : E1, iteratedFDeriv ℝ 1 ((φ.fderivApply (toE1 1) : E1 → ℝ)) x
      (fun _ ↦ toE1 1) = iteratedFDeriv ℝ 2 (φ : E1 → ℝ) x (fun _ ↦ toE1 1) := by
    intro x
    rw [φ.contDiff.iteratedFDeriv_succ_apply_left' 1 (fun _ ↦ toE1 1) x]
    simp [Fin.tail]
  have h1 : ∫ x in (Ω₁ : Set E1), iteratedFDeriv ℝ 1 ((φ.fderivApply (toE1 1) : E1 → ℝ)) x
        (fun _ ↦ toE1 1) • v x ∂volume
      = (-1 : ℝ) ^ 1 • ∫ x in (Ω₁ : Set E1), (φ.fderivApply (toE1 1)) x • w x ∂volume :=
    hw.integral_smul_eq _
  have h2 : ∫ x in (Ω₁ : Set E1), iteratedFDeriv ℝ 2 (φ : E1 → ℝ) x (fun _ ↦ toE1 1) • v x ∂volume
      = (-1 : ℝ) ^ 2 • ∫ x in (Ω₁ : Set E1), φ x • z x ∂volume := hz.integral_smul_eq φ
  simp only [e1] at h1
  change ∫ x in (Ω₁ : Set E1), iteratedFDeriv ℝ 1 (φ : E1 → ℝ) x (fun _ ↦ toE1 1) • w x ∂volume
      = (-1 : ℝ) ^ 1 • ∫ x in (Ω₁ : Set E1), φ x • z x ∂volume
  have h3 := h1.symm.trans h2
  simp only [TestFunction.fderivApply_coe, iteratedFDeriv_one_apply, pow_one, pow_two,
    neg_mul, neg_neg, one_mul, smul_eq_mul] at h3 ⊢
  linarith [h3]

/-- A test function on `Ω` taking the value `1` at a prescribed point of `Ω`. -/
theorem exists_testFunction_eq_one {x : E1} (hx : x ∈ (Ω₁ : Set E1)) :
    ∃ φ : 𝓓(Ω₁, ℝ), φ x = 1 := by
  obtain ⟨f, h1, h2, h3, -, h5⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (Ω₁.isOpen.mem_nhds hx)
  exact ⟨⟨f, h3, h2, h1⟩, h5⟩

/-! ### One-dimensional integration by parts -/

/-- **The fundamental theorem of calculus with finitely many exceptional points**: if `g` is
continuous on `[a, b]` and has derivative `g'` at every point of `(a, b)` outside a finite set `T`,
and `g'` is interval integrable, then `∫_a^b g' = g b - g a`. Mathlib's
`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` is the case `T = ∅`; the general case
follows by splitting the interval at each exceptional point. -/
private theorem ftcFinite (T : Finset ℝ) : ∀ {a b : ℝ}, a ≤ b → ∀ {g g' : ℝ → ℝ},
    ContinuousOn g (Icc a b) → (∀ t ∈ Ioo a b, t ∉ T → HasDerivAt g (g' t) t) →
    IntervalIntegrable g' volume a b → ∫ t in a..b, g' t = g b - g a := by
  induction T using Finset.strongInduction with
  | _ T ih =>
    intro a b hab g g' hcont hderiv hint
    by_cases hT : ∃ c ∈ T, c ∈ Ioo a b
    · obtain ⟨c, hcT, hc⟩ := hT
      have hac : a ≤ c := hc.1.le
      have hcb : c ≤ b := hc.2.le
      have hsub : T.erase c ⊂ T := Finset.erase_ssubset hcT
      have hint1 : IntervalIntegrable g' volume a c :=
        hint.mono_set (by rw [uIcc_of_le hab, uIcc_of_le hac]; exact Icc_subset_Icc le_rfl hcb)
      have hint2 : IntervalIntegrable g' volume c b :=
        hint.mono_set (by rw [uIcc_of_le hab, uIcc_of_le hcb]; exact Icc_subset_Icc hac le_rfl)
      have h1 : ∫ t in a..c, g' t = g c - g a := by
        refine ih _ hsub hac (hcont.mono (Icc_subset_Icc le_rfl hcb)) ?_ hint1
        intro t ht htT
        exact hderiv t ⟨ht.1, ht.2.trans hc.2⟩ fun h ↦ htT (Finset.mem_erase.2 ⟨ht.2.ne, h⟩)
      have h2 : ∫ t in c..b, g' t = g b - g c := by
        refine ih _ hsub hcb (hcont.mono (Icc_subset_Icc hac le_rfl)) ?_ hint2
        intro t ht htT
        exact hderiv t ⟨hc.1.trans ht.1, ht.2⟩ fun h ↦ htT (Finset.mem_erase.2 ⟨ht.1.ne', h⟩)
      rw [← integral_add_adjacent_intervals hint1 hint2, h1, h2]
      ring
    · exact integral_eq_sub_of_hasDerivAt_of_le hab hcont
        (fun t ht ↦ hderiv t ht fun h ↦ hT ⟨t, h, ht⟩) hint

/-- **Integration by parts on `[c, d]` with finitely many exceptional points**: for `ψ` of class
`C^1`, `v` continuous on `[c, d]` with derivative `w` outside a finite set,
`∫_c^d ψ' v + ∫_c^d ψ w = ψ(d) v(d) - ψ(c) v(c)`. This is the identity behind Examples 7.1.6 and
7.1.8: the exceptional points are the points where `v` has a corner. -/
private theorem integralByParts {c d : ℝ} (hcd : c ≤ d) (T : Finset ℝ) {v w ψ : ℝ → ℝ}
    (hv : ContinuousOn v (Icc c d)) (hψ : ContDiff ℝ 1 ψ)
    (hd : ∀ t ∈ Ioo c d, t ∉ T → HasDerivAt v (w t) t)
    (hw : IntervalIntegrable w volume c d) :
    (∫ t in c..d, deriv ψ t * v t) + ∫ t in c..d, ψ t * w t = ψ d * v d - ψ c * v c := by
  have hderivψ : ∀ t, HasDerivAt ψ (deriv ψ t) t := fun t ↦
    (hψ.differentiable (by norm_num) t).hasDerivAt
  have hcψ : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
  have h1 : IntervalIntegrable (fun t ↦ deriv ψ t * v t) volume c d :=
    ((hcψ.continuousOn.mul hv).intervalIntegrable_of_Icc hcd)
  have h2 : IntervalIntegrable (fun t ↦ ψ t * w t) volume c d :=
    hw.continuousOn_mul (hψ.continuous.continuousOn)
  rw [← integral_add h1 h2]
  exact ftcFinite T hcd ((hψ.continuous.continuousOn).mul hv)
    (fun t ht htT ↦ (hderivψ t).mul (hd t ht htT)) (h1.add h2)

/-- An integral over `(a, b)` of a function vanishing outside `(p, q) ⊆ (a, b)` is the interval
integral over `[p, q]`. -/
private theorem setIntegral_Ioo_eq_intervalIntegral {a b p q : ℝ} (hpq : p ≤ q)
    (hsub : Ioo p q ⊆ Ioo a b) {f : ℝ → ℝ} (hf : ∀ t ∉ Ioo p q, f t = 0) :
    ∫ t in Ioo a b, f t = ∫ t in p..q, f t := by
  rw [intervalIntegral.integral_of_le hpq,
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht ↦ hf t fun h ↦ ht (hsub h)),
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun t ht ↦ hf t fun h ↦ ht (Ioo_subset_Ioc_self h))]

section Piece

variable {p c : ℝ} {W W₁ Y₁ ψ : ℝ → ℝ}

/-- A function agreeing with `W₁` on `(p, c)` integrates over `[p, c]` like `W₁`. -/
private theorem intervalIntegral_congr_piece (hpc : p < c) (heq : ∀ t ∈ Ioo p c, W t = W₁ t)
    {g : ℝ → ℝ} : ∫ t in p..c, g t * W t = ∫ t in p..c, g t * W₁ t := by
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ae_ne_real c] with t ht htI
  rw [uIoc_of_le hpc.le] at htI
  rw [heq t ⟨htI.1, lt_of_le_of_ne htI.2 ht⟩]

/-- Integration by parts on one piece `[p, c]` of a partition, for a function `W` that agrees on
the open piece with a `C^1` function `W₁` whose derivative is `Y₁`. -/
private theorem integralByParts_piece (hpc : p < c) (hW₁ : ContinuousOn W₁ (Icc p c))
    (hY₁ : ContinuousOn Y₁ (Icc p c)) (hd : ∀ t ∈ Ioo p c, HasDerivAt W₁ (Y₁ t) t)
    (heq : ∀ t ∈ Ioo p c, W t = W₁ t) (hψ : ContDiff ℝ 1 ψ) :
    (∫ t in p..c, deriv ψ t * W t) + ∫ t in p..c, ψ t * Y₁ t = ψ c * W₁ c - ψ p * W₁ p := by
  rw [intervalIntegral_congr_piece hpc heq]
  exact integralByParts hpc.le ∅ hW₁ hψ (fun t ht _ ↦ hd t ht)
    (hY₁.intervalIntegrable_of_Icc hpc.le)

/-- On one piece the integrand `ψ' W` is interval integrable. -/
private theorem intervalIntegrable_piece (hpc : p < c) (hW₁ : ContinuousOn W₁ (Icc p c))
    (heq : ∀ t ∈ Ioo p c, W t = W₁ t) (hψ : ContDiff ℝ 1 ψ) :
    IntervalIntegrable (fun t ↦ deriv ψ t * W t) volume p c := by
  refine IntervalIntegrable.congr_uIoo (f := fun t ↦ deriv ψ t * W₁ t) ?_ fun t ht ↦ ?_
  · exact (((hψ.continuous_deriv le_rfl).continuousOn).mul hW₁).intervalIntegrable_of_Icc hpc.le
  · rw [uIoo_of_le hpc.le] at ht
    rw [heq t ht]

end Piece

/-- An open interval of `ℝ`, read as an open subset of `ℝ^1`. -/
private def opensOfIoo (p q : ℝ) : Opens E1 :=
  ⟨{y : E1 | y 0 ∈ Ioo p q}, isOpen_Ioo.preimage toE1.symm.continuous⟩

@[simp]
private theorem preimage_opensOfIoo (p q : ℝ) :
    toE1 ⁻¹' (opensOfIoo p q : Set E1) = Ioo p q := by
  ext t; simp [opensOfIoo]

/-- A function on `ℝ` integrable over `toE1 ⁻¹' Ω` is locally integrable, read on `Ω ⊆ ℝ^1`. -/
private theorem locallyIntegrableOn_comp {s : Set ℝ} (hpre : toE1 ⁻¹' (Ω₁ : Set E1) = s)
    {U : ℝ → ℝ} (hU : IntegrableOn U s volume) :
    LocallyIntegrableOn (fun y : E1 ↦ U (y 0)) Ω₁ volume := by
  refine IntegrableOn.locallyIntegrableOn ?_
  rw [← toE1.measurePreserving.integrableOn_comp_preimage
    toE1.toHomeomorph.measurableEmbedding, hpre]
  exact hU

/-- An almost-everywhere statement on `ℝ^1`, read on the line. -/
private theorem ae_comp_toE1 {P : E1 → Prop} (h : ∀ᵐ x : E1, P x) : ∀ᵐ t : ℝ, P (toE1 t) := by
  refine ae_of_ae_map toE1.continuous.measurable.aemeasurable ?_
  rwa [toE1.measurePreserving.map_eq]

/-! ### The jump function of Examples 7.1.6 and 7.1.7 -/

/-- The jump `sgn` on `ℝ^1`: `1` where the coordinate is positive and `-1` elsewhere. It is the
weak derivative of `|x|` in Example 7.1.6 and the function of Example 7.1.7. -/
noncomputable def sgnE1 (x : E1) : ℝ := if 0 < x 0 then 1 else -1

/-- The jump `sgn` on `ℝ^1` is measurable. -/
theorem measurable_sgnE1 : Measurable sgnE1 :=
  Measurable.ite (measurableSet_lt measurable_const toE1.symm.continuous.measurable)
    measurable_const measurable_const

/-- The jump `sgn` on `ℝ^1` has absolute value one. -/
theorem norm_sgnE1_le (x : E1) : ‖sgnE1 x‖ ≤ 1 := by
  rw [sgnE1]; split_ifs <;> simp

/-- A function on `ℝ^1` agreeing with the jump `sgn` away from the origin — the value at the origin
being arbitrary — is locally integrable. -/
theorem locallyIntegrable_of_eq_sgnE1 {V : E1 → ℝ}
    (hV : ∀ x : E1, x 0 ≠ 0 → V x = sgnE1 x) : LocallyIntegrable V volume := by
  have hae : V =ᵐ[volume] sgnE1 := by
    filter_upwards [ae_apply_ne_zero] with x hx using hV x hx
  refine locallyIntegrable_of_bound (C := 1)
    (measurable_sgnE1.aestronglyMeasurable.congr hae.symm) ?_
  filter_upwards [hae] with x hx using hx ▸ norm_sgnE1_le x

/-- A function on `ℝ` agreeing with the jump `sgn` away from the origin is interval integrable. -/
theorem intervalIntegrable_of_eq_sgnE1 {V : ℝ → ℝ}
    (hV : ∀ t : ℝ, t ≠ 0 → V t = sgnE1 (toE1 t)) (a b : ℝ) :
    IntervalIntegrable V volume a b := by
  have hae : V =ᵐ[volume] sgnE1 ∘ toE1 := by
    filter_upwards [ae_ne_real 0] with t ht using hV t ht
  refine intervalIntegrable_of_bound (C := 1)
    ((measurable_sgnE1.comp toE1.continuous.measurable).aestronglyMeasurable.congr hae.symm) ?_ a b
  filter_upwards [hae] with t ht using ht ▸ norm_sgnE1_le (toE1 t)

/-- The computation behind Example 7.1.7: against the derivative of a test function on `(-1, 1)`,
the jump `sgn` integrates to `-2 ψ(0)`. -/
theorem integral_deriv_mul_jump {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hm : ψ (-1) = 0) (hp : ψ 1 = 0) {V : ℝ → ℝ}
    (hV : ∀ t : ℝ, t ≠ 0 → V t = sgnE1 (toE1 t)) :
    ∫ t in Ioo (-1 : ℝ) 1, deriv ψ t * V t = -2 * ψ 0 := by
  have hcψ : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
  have hψd : ∀ x, DifferentiableAt ℝ ψ x := hψ.differentiable (by norm_num)
  have hprod : ∀ a b : ℝ, IntervalIntegrable (fun t ↦ deriv ψ t * V t) volume a b :=
    fun a b ↦ (intervalIntegrable_of_eq_sgnE1 hV a b).continuousOn_mul hcψ.continuousOn
  have hsub : ∀ a b : ℝ, ∫ t in a..b, deriv ψ t = ψ b - ψ a := fun a b ↦
    integral_deriv_eq_sub (fun x _ ↦ hψd x) (hcψ.intervalIntegrable _ _)
  have e1 : ∫ t in (-1 : ℝ)..0, deriv ψ t * V t = -(ψ 0 - ψ (-1)) := by
    rw [intervalIntegral.integral_congr_ae (g := fun t ↦ -deriv ψ t) ?_,
      intervalIntegral.integral_neg, hsub]
    filter_upwards [ae_ne_real 0] with t ht htI
    rw [uIoc_of_le (by norm_num)] at htI
    have h : sgnE1 (toE1 t) = -1 := by rw [sgnE1, toE1_apply]; simp [not_lt.2 htI.2]
    rw [hV t ht, h]
    ring
  have e2 : ∫ t in (0 : ℝ)..1, deriv ψ t * V t = ψ 1 - ψ 0 := by
    rw [intervalIntegral.integral_congr_ae (g := fun t ↦ deriv ψ t) ?_, hsub]
    filter_upwards with t htI
    rw [uIoc_of_le (by norm_num)] at htI
    have h : sgnE1 (toE1 t) = 1 := by rw [sgnE1, toE1_apply]; simp [htI.1]
    rw [hV t htI.1.ne', h]
    ring
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num),
    ← integral_add_adjacent_intervals (hprod (-1) 0) (hprod 0 1), e1, e2, hm, hp]
  ring

/-! ### Examples 7.1.6, 7.1.7 and 7.1.8 -/

/-- **Example 7.1.6**: on an interval `(a, b)` containing the origin, the function `v(x) = |x|`,
which is not differentiable at `0` in the classical sense, has the first-order weak derivative
`w = 1` for `x > 0` and `w = -1` for `x < 0`. The value of `w` at the origin is arbitrary: the
hypothesis only constrains `w` off the coordinate hyperplane `x_1 = 0`, which here is the single
point `0`. -/
theorem example_7_1_6 {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    (hΩ : (Ω₁ : Set E1) = {x : E1 | x 0 ∈ Ioo a b})
    {w : E1 → ℝ} (hw : ∀ x : E1, x 0 ≠ 0 → w x = if 0 < x 0 then 1 else -1) :
    definition_7_1_3_multiIndex ![1] (fun x ↦ |x 0|) w Ω₁ := by
  have hab : a ≤ b := (ha.trans hb).le
  have hpre : toE1 ⁻¹' (Ω₁ : Set E1) = Ioo a b := by rw [hΩ]; ext t; simp
  refine transport ((toE1.symm.continuous.abs).locallyIntegrable.locallyIntegrableOn _)
    ((locallyIntegrable_of_eq_sgnE1 hw).locallyIntegrableOn _) ?_
  intro ψ hψ _ hsupp
  rw [hpre] at hsupp ⊢
  have hψa : ψ a = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ (hsupp h).1.false
  have hψb : ψ b = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ (hsupp h).2.false
  have hd : ∀ t ∈ Ioo a b, t ∉ ({0} : Finset ℝ) → HasDerivAt (|·| : ℝ → ℝ) (w (toE1 t)) t := by
    intro t _ ht
    simp only [Finset.mem_singleton] at ht
    rw [hw (toE1 t) (by simpa using ht), toE1_apply]
    rcases lt_or_gt_of_ne ht with h | h
    · simpa [not_lt.2 h.le] using hasDerivAt_abs_neg h
    · simpa [h] using hasDerivAt_abs_pos h
  have hwint : IntervalIntegrable (fun t ↦ w (toE1 t)) volume a b :=
    intervalIntegrable_of_eq_sgnE1 (fun t ht ↦ hw (toE1 t) (by simpa using ht)) a b
  have key := integralByParts hab {0} (v := (|·| : ℝ → ℝ)) (w := fun t ↦ w (toE1 t)) (ψ := ψ)
    continuous_abs.continuousOn (hψ.of_le (by norm_num)) hd hwint
  rw [hψa, hψb] at key
  simp only [zero_mul, sub_self] at key
  rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hab, ← intervalIntegral.integral_of_le hab]
  simp only [toE1_apply]
  linarith [key]

/-- **Example 7.1.7**: the step function `v = -1` on `(-1, 0)` and `v = 1` on `(0, 1)` has no weak
derivative on `Ω = (-1, 1)`. Integration by parts on each half gives `∫_Ω v ∂φ = -2 φ(0)`, so a
weak derivative `w` would satisfy `∫_Ω w φ = 2 φ(0)` for every test function; Lemma 7.1.2 applied on
`Ω \ {0}` then forces `w = 0` a.e. on `Ω`, whence `φ(0) = 0` for every test function, which is
false. So a jump discontinuity destroys weak differentiability. -/
theorem example_7_1_7 (hΩ : (Ω₁ : Set E1) = {x : E1 | x 0 ∈ Ioo (-1) 1})
    {v : E1 → ℝ} (hv : ∀ x : E1, x 0 ≠ 0 → v x = if 0 < x 0 then 1 else -1) :
    ¬ ∃ w : E1 → ℝ, definition_7_1_3_multiIndex ![1] v w Ω₁ := by
  rintro ⟨w, hwd⟩
  rw [definition_7_1_3_multiIndex, multiIndexTuple_dimOne] at hwd
  have hpre : toE1 ⁻¹' (Ω₁ : Set E1) = Ioo (-1 : ℝ) 1 := by rw [hΩ]; ext t; simp
  have hzero : (0 : E1) ∈ (Ω₁ : Set E1) := by rw [hΩ]; norm_num
  -- the defining identity forces `∫_Ω φ w = 2 φ(0)`
  have step1 : ∀ φ : 𝓓(Ω₁, ℝ), ∫ x in (Ω₁ : Set E1), φ x • w x ∂volume = 2 * φ 0 := by
    intro φ
    have h : ∫ x in (Ω₁ : Set E1),
          iteratedFDeriv ℝ 1 (φ : E1 → ℝ) x (fun _ ↦ toE1 1) • v x ∂volume
        = (-1 : ℝ) ^ 1 • ∫ x in (Ω₁ : Set E1), φ x • w x ∂volume := hwd.integral_smul_eq φ
    rw [integral_iteratedFDeriv_mul, hpre] at h
    have hjump : ∫ t in Ioo (-1 : ℝ) 1, deriv ((φ : E1 → ℝ) ∘ toE1) t * v (toE1 t)
        = -2 * φ 0 := by
      refine integral_deriv_mul_jump ((contDiff_comp_toE1 φ).of_le (by norm_num)) ?_ ?_
        (fun t ht ↦ hv (toE1 t) (by simpa using ht))
      · exact image_eq_zero_of_notMem_tsupport fun hm ↦ by
          have := hpre ▸ tsupport_comp_toE1 φ hm; simp at this
      · exact image_eq_zero_of_notMem_tsupport fun hm ↦ by
          have := hpre ▸ tsupport_comp_toE1 φ hm; simp at this
    rw [hjump] at h
    simp only [pow_one, neg_one_smul] at h
    linarith [h]
  -- Lemma 7.1.2 on `Ω \ {0}` makes `w` vanish a.e. there, hence a.e. on `Ω`
  set Ω' : Opens E1 :=
    ⟨(Ω₁ : Set E1) \ ({0} : Set E1), Ω₁.isOpen.sdiff isClosed_singleton⟩ with hΩ'def
  have hsub : (Ω' : Set E1) ⊆ (Ω₁ : Set E1) := Set.sdiff_subset
  have hnull : (Ω' : Set E1) =ᵐ[volume] (Ω₁ : Set E1) :=
    sdiff_ae_eq_self.2 (measure_mono_null inter_subset_right (measure_singleton 0))
  have hzeroΩ' : ∀ᵐ x : E1, x ∈ (Ω' : Set E1) → w x = 0 := by
    refine lemma_7_1_2 (hwd.locallyIntegrableOn_weakDeriv.mono_set hsub) fun φ' ↦ ?_
    have hts : tsupport (φ' : E1 → ℝ) ⊆ (Ω₁ : Set E1) := φ'.tsupport_subset.trans hsub
    have h0 : (φ' : E1 → ℝ) 0 = 0 :=
      image_eq_zero_of_notMem_tsupport fun hm ↦ (φ'.tsupport_subset hm).2 rfl
    have hstep := step1 ⟨φ', φ'.contDiff, φ'.hasCompactSupport, hts⟩
    have hcoe : ((⟨φ', φ'.contDiff, φ'.hasCompactSupport, hts⟩ : 𝓓(Ω₁, ℝ)) : E1 → ℝ) = φ' := rfl
    rw [hcoe, h0, mul_zero] at hstep
    rw [setIntegral_congr_set hnull]
    simpa [mul_comm] using hstep
  have hzeroΩ : ∀ᵐ x : E1, x ∈ (Ω₁ : Set E1) → w x = 0 := by
    filter_upwards [hzeroΩ', ae_apply_ne_zero] with x h1 h2 hxΩ
    exact h1 ⟨hxΩ, fun h ↦ h2 (by rw [h]; rfl)⟩
  -- but then `2 φ(0) = 0` for every test function, and some test function has `φ(0) = 1`
  obtain ⟨φ, hφ⟩ := exists_testFunction_eq_one hzero
  have hint : ∫ x in (Ω₁ : Set E1), φ x • w x ∂volume = 0 := by
    refine integral_eq_zero_of_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' Ω₁.isOpen.measurableSet]
    filter_upwards [hzeroΩ] with x hx hxΩ
    simp [hx hxΩ]
  rw [step1 φ, hφ] at hint
  norm_num at hint

section Partition

variable {N : ℕ} {x : Fin (N + 1) → ℝ} {V W : ℝ → ℝ}

/-- A point of `(x_0, x_N)` other than a node of the partition lies in one of the open
subintervals `(x_i, x_{i+1})`. -/
theorem exists_mem_Ioo_of_strictMono (hx : StrictMono x) {t : ℝ}
    (ht : t ∈ Ioo (x 0) (x (Fin.last N))) (ht' : ∀ i, t ≠ x i) :
    ∃ i : Fin N, t ∈ Ioo (x i.castSucc) (x i.succ) := by
  classical
  have hne : (Finset.univ.filter (fun i : Fin (N + 1) ↦ x i < t)).Nonempty :=
    ⟨0, by simp [ht.1]⟩
  set j := (Finset.univ.filter (fun i : Fin (N + 1) ↦ x i < t)).max' hne with hjdef
  have hjlt : x j < t := by
    have := Finset.max'_mem _ hne
    simpa [← hjdef] using this
  have hjn : (j : ℕ) < N := by
    rcases Nat.lt_or_ge (j : ℕ) N with h | h
    · exact h
    · exact absurd hjlt (not_lt.2 (le_trans ht.2.le
        (hx.monotone (by simpa [Fin.le_def, Fin.last] using h))))
  refine ⟨⟨j, hjn⟩, ?_, ?_⟩
  · simpa [Fin.castSucc, Fin.castAdd, Fin.castLE] using hjlt
  · have hsucc : ((⟨j, hjn⟩ : Fin N).succ) ∉
        Finset.univ.filter (fun i : Fin (N + 1) ↦ x i < t) := by
      intro hmem
      have := Finset.le_max' _ _ hmem
      simp [Fin.le_def, Fin.succ, ← hjdef] at this
    have : ¬ (x ((⟨j, hjn⟩ : Fin N).succ) < t) := by simpa using hsucc
    exact lt_of_le_of_ne (not_lt.1 this) (ht' _)

/-- Inside a closed interval on which `V` is `C^1`, the classical derivative exists. -/
theorem hasDerivAt_of_contDiffOn_Icc {c d : ℝ} (h : ContDiffOn ℝ 1 V (Icc c d))
    {t : ℝ} (ht : t ∈ Ioo c d) : HasDerivAt V (deriv V t) t :=
  ((h.differentiableOn one_ne_zero t (mem_Icc_of_Ioo ht)).differentiableAt
    (Icc_mem_nhds ht.1 ht.2)).hasDerivAt

/-- On a closed interval on which `V` is `C^1`, a function agreeing with `V'` in the interior is
interval integrable: it agrees a.e. with `derivWithin V`, which is continuous there. -/
theorem intervalIntegrable_of_eq_deriv {c d : ℝ} (hcd : c < d)
    (h : ContDiffOn ℝ 1 V (Icc c d)) (hW : ∀ t ∈ Ioo c d, W t = deriv V t) :
    IntervalIntegrable W volume c d := by
  refine IntervalIntegrable.congr_uIoo (f := derivWithin V (Icc c d)) ?_ fun t ht ↦ ?_
  · exact (h.continuousOn_derivWithin (uniqueDiffOn_Icc hcd) le_rfl).intervalIntegrable_of_Icc
      hcd.le
  · rw [uIoo_of_le hcd.le] at ht
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2), hW t ht]

/-- **Example 7.1.8**, first order: let `V ∈ C[a, b]` be piecewise continuously differentiable over
a partition `a = x_0 < x_1 < ⋯ < x_N = b`, so that `V` is `C^1` on each closed subinterval, and let
`W` be `V'` on each open subinterval (its values at the nodes being arbitrary). Then, read on
`Ω = (a, b) ⊆ ℝ^1`, `W` is the first-order weak derivative of `V`. -/
theorem example_7_1_8 (hx : StrictMono x)
    (hΩ : (Ω₁ : Set E1) = {y : E1 | y 0 ∈ Ioo (x 0) (x (Fin.last N))})
    (hV : ContinuousOn V (Icc (x 0) (x (Fin.last N))))
    (hpw : ∀ i : Fin N, ContDiffOn ℝ 1 V (Icc (x i.castSucc) (x i.succ)))
    (hW : ∀ i : Fin N, ∀ t ∈ Ioo (x i.castSucc) (x i.succ), W t = deriv V t) :
    definition_7_1_3_multiIndex ![1] (fun y ↦ V (y 0)) (fun y ↦ W (y 0)) Ω₁ := by
  classical
  have hab : x 0 ≤ x (Fin.last N) := hx.monotone (Fin.zero_le _)
  have hpre : toE1 ⁻¹' (Ω₁ : Set E1) = Ioo (x 0) (x (Fin.last N)) := by rw [hΩ]; ext t; simp
  -- interval integrability of `W`, piece by piece and then over the whole interval
  have hWi : ∀ i : Fin N, IntervalIntegrable W volume (x i.castSucc) (x i.succ) := fun i ↦
    intervalIntegrable_of_eq_deriv (hx (by simp [Fin.lt_def])) (hpw i) (hW i)
  have hWint : IntervalIntegrable W volume (x 0) (x (Fin.last N)) := by
    have step : ∀ k : ℕ, ∀ hk : k < N + 1, IntervalIntegrable W volume (x 0) (x ⟨k, hk⟩) := by
      intro k
      induction k with
      | zero => intro hk; simp [IntervalIntegrable, show (⟨0, hk⟩ : Fin (N + 1)) = 0 from rfl]
      | succ m ih =>
        intro hk
        refine (ih (by omega)).trans ?_
        have h := hWi ⟨m, by omega⟩
        convert h using 2 <;> simp [Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ]
    have h := step N (by omega)
    convert h using 2
    simp [Fin.last]
  -- the classical derivative away from the nodes
  have hd : ∀ t ∈ Ioo (x 0) (x (Fin.last N)), t ∉ Finset.image x Finset.univ →
      HasDerivAt V (W t) t := by
    intro t ht htT
    obtain ⟨i, hi⟩ := exists_mem_Ioo_of_strictMono hx ht
      (fun i hi ↦ htT (Finset.mem_image.2 ⟨i, Finset.mem_univ i, hi.symm⟩))
    rw [hW i t hi]
    exact hasDerivAt_of_contDiffOn_Icc (hpw i) hi
  -- local integrability of `V` and `W` on `Ω`
  have hcomp : ∀ U : ℝ → ℝ, IntegrableOn U (Ioo (x 0) (x (Fin.last N))) volume →
      LocallyIntegrableOn (fun y : E1 ↦ U (y 0)) Ω₁ volume := by
    intro U hU
    refine IntegrableOn.locallyIntegrableOn ?_
    rw [← toE1.measurePreserving.integrableOn_comp_preimage
      toE1.toHomeomorph.measurableEmbedding, hpre]
    exact hU
  refine transport (hcomp V (hV.integrableOn_Icc.mono_set Ioo_subset_Icc_self))
    (hcomp W ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab).1 hWint)) ?_
  intro ψ hψ _ hsupp
  rw [hpre] at hsupp ⊢
  have hψa : ψ (x 0) = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ (hsupp h).1.false
  have hψb : ψ (x (Fin.last N)) = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ (hsupp h).2.false
  have key := integralByParts hab (Finset.image x Finset.univ) (v := V) (w := W) (ψ := ψ)
    hV (hψ.of_le (by norm_num)) hd hWint
  rw [hψa, hψb] at key
  simp only [zero_mul, sub_self] at key
  rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hab, ← intervalIntegral.integral_of_le hab]
  simp only [toE1_apply]
  linarith [key]

end Partition

/-! ### A jump kills weak differentiability

The obstruction of Example 7.1.7, in the form needed for the second half of Example 7.1.8: a
function that is continuously differentiable on `(p, c)` and on `(c, q)` and has a weak derivative
on an interval containing them takes the same one-sided limit at `c` from either side. -/

section Jump

variable {a b p c q : ℝ} {W W₁ W₂ Y₁ Y₂ : ℝ → ℝ} {z : E1 → ℝ}

/-- An almost-everywhere statement on an open piece `(p, c)` transfers to `Ι p c`, the two sets
differing by the single point `c`. -/
private theorem ae_uIoc_of_ae_Ioo (hpc : p < c) {f g : ℝ → ℝ}
    (h : ∀ᵐ t : ℝ, t ∈ Ioo p c → f t = g t) : ∀ᵐ t : ℝ, t ∈ Ι p c → f t = g t := by
  filter_upwards [h, ae_ne_real c] with t ht htne htI
  rw [uIoc_of_le hpc.le] at htI
  exact ht ⟨htI.1, lt_of_le_of_ne htI.2 htne⟩

/-- The same statement as an almost-everywhere equality for the restricted measure. -/
private theorem ae_restrict_of_ae_Ioo (hpc : p < c) {f g : ℝ → ℝ}
    (h : ∀ᵐ t : ℝ, t ∈ Ioo p c → f t = g t) : f =ᵐ[volume.restrict (Ι p c)] g :=
  (ae_restrict_iff' measurableSet_uIoc).2 (ae_uIoc_of_ae_Ioo hpc h)

/-- On an open piece on which `W` is classically continuously differentiable, every weak
derivative of `W` agrees almost everywhere with the classical derivative. -/
private theorem ae_eq_of_hasDerivAt_piece (hpc : p < c) (hsub : Ioo p c ⊆ Ioo a b)
    (hΩ : (Ω₁ : Set E1) = {y : E1 | y 0 ∈ Ioo a b})
    (hW₁ : ContinuousOn W₁ (Icc p c)) (hY₁ : ContinuousOn Y₁ (Icc p c))
    (hd : ∀ t ∈ Ioo p c, HasDerivAt W₁ (Y₁ t) t) (heq : ∀ t ∈ Ioo p c, W t = W₁ t)
    (hz : definition_7_1_3_multiIndex ![1] (fun y ↦ W (y 0)) z Ω₁) :
    ∀ᵐ t : ℝ, t ∈ Ioo p c → z (toE1 t) = Y₁ t := by
  have hle : opensOfIoo p c ≤ Ω₁ := fun y hy ↦ show y ∈ (Ω₁ : Set E1) by
    rw [hΩ]; exact hsub hy
  have hz' : definition_7_1_3_multiIndex ![1] (fun y ↦ W (y 0)) z (opensOfIoo p c) :=
    HasWeakIteratedLineDerivOn.mono hz hle
  have hY : definition_7_1_3_multiIndex ![1] (fun y ↦ W (y 0))
      (fun y ↦ Y₁ (y 0)) (opensOfIoo p c) := by
    refine transport hz'.locallyIntegrableOn
      (locallyIntegrableOn_comp (preimage_opensOfIoo p c)
        ((hY₁.integrableOn_Icc).mono_set Ioo_subset_Icc_self)) ?_
    intro ψ hψ _ hsupp
    rw [preimage_opensOfIoo] at hsupp ⊢
    simp only [toE1_apply]
    have hψp : ψ p = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ (hsupp h).1.false
    have hψc : ψ c = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ (hsupp h).2.false
    have hz1 : ∀ t ∉ Ioo p c, deriv ψ t * W t = 0 := fun t ht ↦ by
      rw [Function.notMem_support.1 fun h ↦ ht (hsupp (support_deriv_subset h)), zero_mul]
    have hz2 : ∀ t ∉ Ioo p c, ψ t * Y₁ t = 0 := fun t ht ↦ by
      rw [image_eq_zero_of_notMem_tsupport fun h ↦ ht (hsupp h), zero_mul]
    rw [setIntegral_Ioo_eq_intervalIntegral hpc.le subset_rfl hz1,
      setIntegral_Ioo_eq_intervalIntegral hpc.le subset_rfl hz2]
    have key := integralByParts_piece hpc hW₁ hY₁ hd heq (hψ.of_le (by norm_num))
    rw [hψp, hψc] at key
    simp only [zero_mul, sub_self] at key
    linarith [key]
  have hae := HasWeakIteratedLineDerivOn.ae_eq hz' hY
  filter_upwards [ae_comp_toE1 hae] with t ht htI
  exact ht htI

/-- **A jump destroys weak differentiability**: if `W` agrees with a continuously differentiable
`W₁` on `(p, c)` and with a continuously differentiable `W₂` on `(c, q)`, and `W` has a weak
derivative on `Ω = (a, b) ⊇ (p, q)`, then `W₁(c) = W₂(c)`. Example 7.1.7 is the case
`W₁ = -1`, `W₂ = 1`. -/
private theorem eq_of_hasWeakDeriv_of_jump (hpc : p < c) (hcq : c < q)
    (hsub : Ioo p q ⊆ Ioo a b) (hΩ : (Ω₁ : Set E1) = {y : E1 | y 0 ∈ Ioo a b})
    (hW₁ : ContinuousOn W₁ (Icc p c)) (hY₁ : ContinuousOn Y₁ (Icc p c))
    (hd₁ : ∀ t ∈ Ioo p c, HasDerivAt W₁ (Y₁ t) t) (heq₁ : ∀ t ∈ Ioo p c, W t = W₁ t)
    (hW₂ : ContinuousOn W₂ (Icc c q)) (hY₂ : ContinuousOn Y₂ (Icc c q))
    (hd₂ : ∀ t ∈ Ioo c q, HasDerivAt W₂ (Y₂ t) t) (heq₂ : ∀ t ∈ Ioo c q, W t = W₂ t)
    (hz : definition_7_1_3_multiIndex ![1] (fun y ↦ W (y 0)) z Ω₁) :
    W₁ c = W₂ c := by
  have hpq : p ≤ q := (hpc.trans hcq).le
  have hsubl : Ioo p c ⊆ Ioo a b := (Ioo_subset_Ioo le_rfl hcq.le).trans hsub
  have hsubr : Ioo c q ⊆ Ioo a b := (Ioo_subset_Ioo hpc.le le_rfl).trans hsub
  have hA := ae_eq_of_hasDerivAt_piece hpc hsubl hΩ hW₁ hY₁ hd₁ heq₁ hz
  have hB := ae_eq_of_hasDerivAt_piece hcq hsubr hΩ hW₂ hY₂ hd₂ heq₂ hz
  -- a bump function equal to `1` at `c` and supported in `(p, q)`
  obtain ⟨ψ, hts, hcs, hψ, -, hψc⟩ := exists_contDiff_tsupport_subset (n := ⊤)
    (isOpen_Ioo.mem_nhds (show c ∈ Ioo p q from ⟨hpc, hcq⟩))
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  have hψp : ψ p = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ (hts h).1.false
  have hψq : ψ q = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ (hts h).2.false
  have hpre : toE1 ⁻¹' (Ω₁ : Set E1) = Ioo a b := by rw [hΩ]; ext t; simp
  -- the defining identity, localized to `[p, q]` and split at `c`
  have hM := transport_symm hz hψ hcs (by rw [hpre]; exact hts.trans hsub)
  rw [hpre] at hM
  simp only [toE1_apply] at hM
  have hz1 : ∀ t ∉ Ioo p q, deriv ψ t * W t = 0 := fun t ht ↦ by
    rw [Function.notMem_support.1 fun h ↦ ht (hts (support_deriv_subset h)), zero_mul]
  have hz2 : ∀ t ∉ Ioo p q, ψ t * z (toE1 t) = 0 := fun t ht ↦ by
    rw [image_eq_zero_of_notMem_tsupport fun h ↦ ht (hts h), zero_mul]
  rw [setIntegral_Ioo_eq_intervalIntegral hpq hsub hz1,
    setIntegral_Ioo_eq_intervalIntegral hpq hsub hz2] at hM
  -- integrability of `ψ z` on each piece, through `hA` and `hB`
  have hA' : ∀ᵐ t : ℝ, t ∈ Ioo p c → ψ t * Y₁ t = ψ t * z (toE1 t) := by
    filter_upwards [hA] with t ht htI; rw [ht htI]
  have hB' : ∀ᵐ t : ℝ, t ∈ Ioo c q → ψ t * Y₂ t = ψ t * z (toE1 t) := by
    filter_upwards [hB] with t ht htI; rw [ht htI]
  have hiz₁ : IntervalIntegrable (fun t ↦ ψ t * z (toE1 t)) volume p c :=
    IntervalIntegrable.congr_ae
      ((hY₁.intervalIntegrable_of_Icc hpc.le).continuousOn_mul hψ.continuous.continuousOn)
      (ae_restrict_of_ae_Ioo hpc hA')
  have hiz₂ : IntervalIntegrable (fun t ↦ ψ t * z (toE1 t)) volume c q :=
    IntervalIntegrable.congr_ae
      ((hY₂.intervalIntegrable_of_Icc hcq.le).continuousOn_mul hψ.continuous.continuousOn)
      (ae_restrict_of_ae_Ioo hcq hB')
  rw [← integral_add_adjacent_intervals
      (intervalIntegrable_piece hpc hW₁ heq₁ hψ1) (intervalIntegrable_piece hcq hW₂ heq₂ hψ1),
    ← integral_add_adjacent_intervals hiz₁ hiz₂] at hM
  -- replace `z` by the classical derivative on each piece
  have e₁ : ∫ t in p..c, ψ t * z (toE1 t) = ∫ t in p..c, ψ t * Y₁ t :=
    (intervalIntegral.integral_congr_ae (ae_uIoc_of_ae_Ioo hpc hA')).symm
  have e₂ : ∫ t in c..q, ψ t * z (toE1 t) = ∫ t in c..q, ψ t * Y₂ t :=
    (intervalIntegral.integral_congr_ae (ae_uIoc_of_ae_Ioo hcq hB')).symm
  rw [e₁, e₂] at hM
  -- integration by parts on each piece
  have k₁ := integralByParts_piece hpc hW₁ hY₁ hd₁ heq₁ hψ1
  have k₂ := integralByParts_piece hcq hW₂ hY₂ hd₂ heq₂ hψ1
  rw [hψp, hψc] at k₁
  rw [hψq, hψc] at k₂
  simp only [zero_mul, sub_zero, one_mul, zero_sub] at k₁ k₂
  linarith [hM, k₁, k₂]

end Jump

section SecondOrder

variable {N : ℕ} {x : Fin (N + 1) → ℝ} {V W : ℝ → ℝ}

/-- **Example 7.1.8**, second order: let `V ∈ C[a, b]` be piecewise twice continuously
differentiable over a partition `a = x_0 < ⋯ < x_N = b`, and let `W` be `V'` on each open
subinterval. If `V` has a second-order weak derivative on `Ω = (a, b) ⊆ ℝ^1` then the one-sided
derivatives of `V` agree at every interior node, `V'(x_i-) = V'(x_i+)`; the one-sided derivatives
are the `derivWithin` of `V` on the two closed subintervals meeting at the node, and an interior
node is one carried by two consecutive subintervals `i` and `j`. -/
theorem example_7_1_8_second_order (hx : StrictMono x)
    (hΩ : (Ω₁ : Set E1) = {y : E1 | y 0 ∈ Ioo (x 0) (x (Fin.last N))})
    (hV : ContinuousOn V (Icc (x 0) (x (Fin.last N))))
    (hpw : ∀ i : Fin N, ContDiffOn ℝ 2 V (Icc (x i.castSucc) (x i.succ)))
    (hW : ∀ i : Fin N, ∀ t ∈ Ioo (x i.castSucc) (x i.succ), W t = deriv V t)
    {z : E1 → ℝ} (hz : definition_7_1_3_multiIndex ![2] (fun y ↦ V (y 0)) z Ω₁)
    (i j : Fin N) (hij : i.succ = j.castSucc) :
    derivWithin V (Icc (x i.castSucc) (x i.succ)) (x i.succ)
      = derivWithin V (Icc (x j.castSucc) (x j.succ)) (x j.castSucc) := by
  -- the first-order weak derivative, and the bridge from the second-order one to it
  have hw : definition_7_1_3_multiIndex ![1] (fun y ↦ V (y 0)) (fun y ↦ W (y 0)) Ω₁ :=
    example_7_1_8 hx hΩ hV (fun k ↦ (hpw k).of_le (by norm_num)) hW
  have hzw : definition_7_1_3_multiIndex ![1] (fun y ↦ W (y 0)) z Ω₁ := secondOrder_bridge hw hz
  have hpc : x i.castSucc < x i.succ := hx (by simp [Fin.lt_def])
  have hcq : x j.castSucc < x j.succ := hx (by simp [Fin.lt_def])
  have hsub : Ioo (x i.castSucc) (x j.succ) ⊆ Ioo (x 0) (x (Fin.last N)) :=
    Ioo_subset_Ioo (hx.monotone (Fin.zero_le _)) (hx.monotone (Fin.le_last _))
  -- on each closed piece `W` is the `C^1` function `derivWithin V`
  have piece : ∀ k : Fin N,
      ContinuousOn (derivWithin V (Icc (x k.castSucc) (x k.succ)))
        (Icc (x k.castSucc) (x k.succ)) ∧
      ContinuousOn (derivWithin (derivWithin V (Icc (x k.castSucc) (x k.succ)))
        (Icc (x k.castSucc) (x k.succ))) (Icc (x k.castSucc) (x k.succ)) ∧
      (∀ t ∈ Ioo (x k.castSucc) (x k.succ),
        HasDerivAt (derivWithin V (Icc (x k.castSucc) (x k.succ)))
          (derivWithin (derivWithin V (Icc (x k.castSucc) (x k.succ)))
            (Icc (x k.castSucc) (x k.succ)) t) t) ∧
      (∀ t ∈ Ioo (x k.castSucc) (x k.succ),
        W t = derivWithin V (Icc (x k.castSucc) (x k.succ)) t) := by
    intro k
    have hlt : x k.castSucc < x k.succ := hx (by simp [Fin.lt_def])
    have hu : UniqueDiffOn ℝ (Icc (x k.castSucc) (x k.succ)) := uniqueDiffOn_Icc hlt
    have h1 : ContDiffOn ℝ 1 (derivWithin V (Icc (x k.castSucc) (x k.succ)))
        (Icc (x k.castSucc) (x k.succ)) := (hpw k).derivWithin hu (by norm_num)
    refine ⟨h1.continuousOn, h1.continuousOn_derivWithin hu le_rfl, fun t ht ↦ ?_, fun t ht ↦ ?_⟩
    · have hd := hasDerivAt_of_contDiffOn_Icc h1 ht
      rwa [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
    · rw [hW k t ht, derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
  obtain ⟨hW₁, hY₁, hd₁, heq₁⟩ := piece i
  obtain ⟨hW₂, hY₂, hd₂, heq₂⟩ := piece j
  rw [← hij] at hW₂ hY₂ hd₂ heq₂ hcq ⊢
  exact eq_of_hasWeakDeriv_of_jump hpc hcq hsub hΩ hW₁ hY₁ hd₁ heq₁ hW₂ hY₂ hd₂ heq₂ hzw

end SecondOrder

end OneDimensional

end AtkinsonHan.Chapter07
