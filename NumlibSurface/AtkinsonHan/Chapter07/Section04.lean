import Mathlib.Analysis.Distribution.Sobolev
import Numlib.Analysis.Sobolev.FourierCharacterization
import NumlibSurface.AtkinsonHan.Chapter07.Section03

/-!
# Atkinson–Han §7.4: the Fourier characterization of `H^k(ℝ^d)`

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §7.4.

Theorem 7.4.1 is here, in the two readings of Definition 7.2.2 that the chapter carries.
`theorem_7_4_1_complex` is the statement for the complex-valued functions that §7.4 allows
throughout ("All the functions in this section are allowed to be complex-valued"): an
`L^2(ℝ^d)` function lies in `W^{k,2}(ℝ^d)`, cut out by the weak derivatives `∂^α v` of order
`|α| ≤ k`, exactly when `(1 + |ξ|^2)^{k/2} ℱv` lies in `L^2(ℝ^d)`. `theorem_7_4_1` is the same
statement for a real-valued `v`, phrased over `definition_7_2_2_multiIndex`, with `ℱv` the Fourier
transform of the complexification of `v`. Both come from the backbone bridge of
`Numlib/Analysis/Sobolev/Tempered.lean`, which identifies the space of Definition 7.2.2 on the
whole space with Mathlib's Bessel potential space, composed with `equation_7_4_2`.

`equation_7_4_2` is the book's (7.4.2), which *defines* `H^s(ℝ^d)` for arbitrary real `s` by the
Fourier condition: for `v ∈ L^2(ℝ^d)` and `s ≥ 0`, `(1 + |ξ|^2)^{s/2} ℱv` lies in `L^2(ℝ^d)` —
`ℱv` being the `L^2` Fourier transform of `v` — exactly when `v` lies in the Bessel potential space
`TemperedDistribution.MemSobolev s 2`, the tempered distributions whose Bessel potential
`(1 - (2π)^{-2} Δ)^{s/2}` is an `L^2` function, which is the `H^s(ℝ^d)` Mathlib supports.
`equation_7_4_2_norm` is the matching norm identity: the `L^2` norm of the Bessel potential of `v`
*equals* — not merely is equivalent to — the `L^2` norm of `(1 + |ξ|^2)^{s/2} ℱv`, by Plancherel.
`s < 0` is excluded only because the proof reads the symbol off the `L^2` representative by
multiplying back by `(1 + |ξ|^2)^{-s/2}`, which is bounded exactly when `s ≥ 0`. Both are the
whole-space theorems of `Numlib/Analysis/Sobolev/FourierCharacterization.lean` at `E = ℝ^d`.

The book's (7.4.1), the *equivalence* of `‖(1 + |ξ|^2)^{k/2} ℱv‖_{L^2}` with the Sobolev norm
`[∑_{|α| ≤ k} ‖∂^α v‖_{L^2}^2]^{1/2}` of Definition 7.2.2, is a separate statement from
Theorem 7.4.1's membership criterion — which goes through Mathlib's
`TemperedDistribution.MemSobolev.fourierMultiplierCLM_of_bounded`, a soft statement about bounded
symbols that carries no constants. It is `equation_7_4_1`, with `equation_7_4_1_complex` its
complex-valued form, and it rests on two things. The first is **Exercise 7.4.2**, the two-sided
symbol inequality `c₁ (∑_{|α| ≤ k} |ξ^α|²)^{1/2} ≤ (1 + |ξ|²)^{k/2} ≤ c₂ (∑_{|α| ≤ k}
|ξ^α|²)^{1/2}`, which is `exercise_7_4_2`; the lower bound needs no multinomial expansion, only
the largest coordinate. The second is the Fourier transform of a weak derivative on the whole
space, `ℱ(∂^α v) = (2πiξ)^α ℱv`, which is `fourier_weakDeriv_aeEq` — Mathlib's
`TemperedDistribution.fourier_lineDerivOp_eq` iterated (`fourier_iteratedLineDerivOp_eq`), pushed
onto the `L²` representatives by the injectivity of `MeasureTheory.Lp.toTemperedDistributionCLM`.
Plancherel then turns `∑_{|α| ≤ k} ‖∂^α v‖²_{L²}` into `∫ (∑_{|α| ≤ k} (2π)^{2|α|} |ξ^α|²) |ℱv|²`
and the symbol inequality compares it with `∫ (1 + |ξ|²)^k |ℱv|²`.

All of this is general — for any orthonormal basis of a finite-dimensional real inner product
space — and lives in the backbone: the Fourier transform of a weak derivative in
`Numlib/Analysis/Sobolev/Tempered.lean`, the symbol inequality
(`OrthonormalBasis.exists_bounds_rpow_one_add_norm_sq`) and the norm equivalence
(`OrthonormalBasis.exists_norm_equiv_eLpNorm_symbol_mul_fourier`) in
`Numlib/Analysis/Sobolev/FourierCharacterization.lean`. What remains here is the book's notation
`ξ^α = ∏ ξ_i^{α_i}` (`xiPow`), the standard basis, and the real-valued reading.

Example 7.4.2, `H^k(Ω) ↪ C(Ω̄)` for `k > d/2`, is here as `example_7_4_2` on a bounded extension
domain (the book's Lipschitz domain, the `C¹` domains of Definition 7.2.1 included through
`isSobolevExtensionDomainAll_of_definition_7_2_1`), but *not* by the book's route: the book
proves it by the Fourier characterization on `ℝ^d` (Step 1), the density of Theorem 7.3.4
(Step 2) and the extension operator (Step 3); here it is the Sobolev embedding of Theorem 7.3.8 (c)
— Morrey's theorem on `ℝ^d` through the order-one extension operator, in
`Numlib/Analysis/Sobolev/DenyLions.lean` — which is the shorter route and needs the extension
operator at order one only. The book's Step 3 at order `k` is available as
`theorem_7_3_5_order` of §7.3; Stein's universal operator, one for all `k` and `p` on a
Lipschitz domain, is not formalized (the `## Not formalized here` section of
`NumlibSurface/AtkinsonHan/Chapter07/Section03.lean`).

Example 7.4.3, the interpolation inequality `‖v‖_{C(Ω̄)} ≤ c ‖v‖_{H^d}^{1/2} ‖v‖_{L^2}^{1/2}`
(7.4.4), is here in its whole-space form `example_7_4_3_whole_space` (and
`example_7_4_3_whole_space_complex`), which is the case the book's proof reduces to and proves by
the Fourier route: the continuous representative of `v ∈ H^d(ℝ^d)` is the inverse Fourier
integral of `ℱv ∈ L¹` (`exists_continuous_ae_eq_of_integrable_fourier`, with
`fourierInv_ae_eq_of_toTemperedDistribution_eq` identifying the pointwise inverse Fourier integral
of an `L¹` function with the `L²` inverse through the tempered distributions), so
`|v(x)| ≤ ∫ |ℱv|`; the Cauchy–Schwarz inequality against the scaled weight `(1 + λ|ξ|²)^{±d/2}`
(the backbone's `sq_lintegral_enorm_le_mul`, `sq_toReal_lintegral_enorm_fourier_le` in
`Numlib/Analysis/Sobolev/FourierCharacterization`) with (7.4.1) on the Fourier side; and the
choice `λ = (‖v‖_{L²}/‖v‖_{H^d})^{2/d}` (`exists_rpow_neg_half_mul_add_eq`).

The domain form is `example_7_4_3`, on a bounded `C^{d+1}` domain where the book has a Lipschitz
domain — the chapter's standing restriction. Its Step 3, the transfer to `Ω`, needs an
extension `Ev ∈ H^{d+1}(ℝ^{d+1})` bounded by `‖v‖_{H^{d+1}(Ω)}` *and simultaneously* by
`‖v‖_{L²(Ω)}` in `L²(ℝ^{d+1})`; the book takes it from Stein's universal operator, and here it is
`theorem_7_3_5_order_lp` of §7.3, the order-`(d+1)` reflection operator with its `L^p` bound — the
reflection being a finite sum of dilations, it is bounded on `L^p` as well as on `W^{k,p}`. Two
private helpers do the plumbing: `exists_lp_data_of_top` moves an element of the typed
`W^{d+1,2}(ℝ^{d+1})` to the `L²(ℝ^{d+1})` data that `example_7_4_3_whole_space` consumes, and
`example_7_4_3_whole_space_typed` is the whole-space inequality restated over that type.
Exercises 7.4.3 and 7.4.4 are not nodes (exercises are not formalized in this round).
-/

open FourierTransform LineDeriv MeasureTheory TemperedDistribution TopologicalSpace

open scoped ENNReal NNReal SchwartzMap

namespace AtkinsonHan.Chapter07

/-! ### The Fourier definition (7.4.2) of `H^s(ℝ^d)` -/

variable {d : ℕ}

/-- **(7.4.2)**, the definition of `H^s(ℝ^d)` by the Fourier condition: for `v ∈ L^2(ℝ^d)` and a
real `s ≥ 0`, `(1 + |ξ|^2)^{s/2} ℱv` lies in `L^2(ℝ^d)` exactly when `v` lies in `H^s(ℝ^d)`.

`H^s(ℝ^d)` is read here as `TemperedDistribution.MemSobolev s 2`, the Bessel potential space: the
distributions whose Bessel potential of order `s` is an `L^2` function. At `s = 0` this is `L^2`
itself, by `TemperedDistribution.memSobolev_zero_iff`. This is *not* Theorem 7.4.1, whose left-hand
side is the `W^{k,2}(ℝ^d)` of `definition_7_2_2_multiIndex`, cut out by the weak derivatives; that
theorem is `theorem_7_4_1`, and it is this display composed with the bridge of
`Numlib/Analysis/Sobolev/Tempered.lean`. The proof is the backbone's
`TemperedDistribution.memSobolev_two_iff_memLp_symbol_mul_fourier`. -/
theorem equation_7_4_2 {s : ℝ} (hs : 0 ≤ s)
    (v : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    MemSobolev s 2 (v : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) ↔
      MemLp (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * (𝓕 v) ξ) 2 volume :=
  memSobolev_two_iff_memLp_symbol_mul_fourier hs v

/-- **The norm that goes with (7.4.2)**: for `v ∈ L^2(ℝ^d)` and `s ≥ 0`, if the Bessel potential of
order `s` of `v` is the `L^2` function `w` — so that `‖w‖_{L^2}` is the `H^s(ℝ^d)` norm of `v` in
the Bessel-potential reading — then

`‖w‖_{L^2(ℝ^d)} = ‖(1 + |ξ|^2)^{s/2} ℱv‖_{L^2(ℝ^d)}`,

by Plancherel (`TemperedDistribution.norm_eq_eLpNorm_symbol_mul_fourier_of_besselPotential_eq`).
This is not the book's (7.4.1), which is the *equivalence* of the right-hand side with the Sobolev
norm `[∑_{|α| ≤ k} ‖∂^α v‖_{L^2}^2]^{1/2}` of Definition 7.2.2, `equation_7_4_1`. -/
theorem equation_7_4_2_norm {s : ℝ} (hs : 0 ≤ s)
    {v w : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))}
    (hw : besselPotential (EuclideanSpace ℝ (Fin d)) ℂ s (v : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) =
      (w : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ))) :
    ‖w‖ =
      (eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * (𝓕 v) ξ) 2 volume).toReal :=
  norm_eq_eLpNorm_symbol_mul_fourier_of_besselPotential_eq hs hw

/-! ### Theorem 7.4.1 -/

/-- **Theorem 7.4.1**, for the complex-valued functions that §7.4 allows throughout: a function
`v ∈ L^2(ℝ^d)` belongs to `H^k(ℝ^d) = W^{k,2}(ℝ^d)` — Definition 7.2.2, so cut out by the weak
derivatives `∂^α v` of order `|α| ≤ k` — exactly when `(1 + |ξ|^2)^{k/2} ℱv ∈ L^2(ℝ^d)`.

The left-hand side is `MemSobolevMultiIndex (stdBasis d) v k 2 ⊤ volume`, which is
`definition_7_2_2_multiIndex k 2 ⊤` read for complex-valued functions; `theorem_7_4_1` is the
real-valued form, over `definition_7_2_2_multiIndex` itself. The proof composes `equation_7_4_2`,
which is the Fourier condition against Mathlib's Bessel potential space, with the identification of
that space with `W^{k,2}(ℝ^d)` in `Numlib/Analysis/Sobolev/Tempered.lean`. -/
theorem theorem_7_4_1_complex {k : ℕ} (v : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    MemSobolevMultiIndex (stdBasis d) (v : EuclideanSpace ℝ (Fin d) → ℂ) k 2 ⊤ volume ↔
      MemLp (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (𝓕 v) ξ) 2 volume := by
  rw [← equation_7_4_2 (by positivity) v]
  exact (TemperedDistribution.memSobolev_iff_memSobolevMultiIndex
    (EuclideanSpace.basisFun (Fin d) ℝ)).symm

/-- **Theorem 7.4.1**: a real function `v ∈ L^2(ℝ^d)` belongs to `H^k(ℝ^d)`, the `W^{k,2}(ℝ^d)` of
Definition 7.2.2, exactly when `(1 + |ξ|^2)^{k/2} ℱv ∈ L^2(ℝ^d)`.

Since the Fourier transform is complex, `ℱv` is read as the Fourier transform of the
complexification `Complex.ofRealCLM.compLp v` of `v`; §7.4 of the book allows the functions to be
complex-valued throughout, and `theorem_7_4_1_complex` is the statement for those. The *norm*
equivalence (7.4.1) that the book states next is the separate, open, `equation_7_4_1`. -/
theorem theorem_7_4_1 {k : ℕ} (v : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    definition_7_2_2_multiIndex k 2 ⊤ (v : EuclideanSpace ℝ (Fin d) → ℝ) ↔
      MemLp (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ)
        * (𝓕 (Complex.ofRealCLM.compLp v)) ξ) 2 volume := by
  rw [← theorem_7_4_1_complex (Complex.ofRealCLM.compLp v)]
  have hae : ((Complex.ofRealCLM.compLp v : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
      : EuclideanSpace ℝ (Fin d) → ℂ)
        =ᵐ[volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin d))) : Set _)]
      fun x ↦ (((v : EuclideanSpace ℝ (Fin d) → ℝ) x : ℝ) : ℂ) := by
    rw [show ((⊤ : Opens (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d)))
      = Set.univ from rfl, Measure.restrict_univ]
    filter_upwards [Complex.ofRealCLM.coeFn_compLp v] with x hx using hx
  exact ⟨fun h ↦ (memSobolevMultiIndex_ofReal_iff.2 h).congr_ae hae.symm,
    fun h ↦ memSobolevMultiIndex_ofReal_iff.1 (h.congr_ae hae)⟩

/-! ### (7.4.1): the norm equivalence -/

section NormEquivalence

variable {d k : ℕ}

/-- The monomial `ξ^α = ∏_i ξ_i^{α_i}` of the multi-index `α`. -/
def xiPow (α : Fin d → ℕ) (ξ : EuclideanSpace ℝ (Fin d)) : ℝ := ∏ i, ξ i ^ α i

/-- `ξ^α` is the backbone's monomial `OrthonormalBasis.coordMonomial` in the standard basis. -/
theorem xiPow_eq_coordMonomial (α : Fin d → ℕ) (ξ : EuclideanSpace ℝ (Fin d)) :
    xiPow α ξ = (EuclideanSpace.basisFun (Fin d) ℝ).coordMonomial α ξ := by
  simp [xiPow, OrthonormalBasis.coordMonomial, EuclideanSpace.inner_single_right]

/-- **Exercise 7.4.2**: there are `c₁, c₂ > 0` with
`c₁ (∑_{|α| ≤ k} |ξ^α|²)^{1/2} ≤ (1 + |ξ|²)^{k/2} ≤ c₂ (∑_{|α| ≤ k} |ξ^α|²)^{1/2}` for every
`ξ ∈ ℝ^d`. This is the two-sided symbol inequality that turns Plancherel's identity into the norm
equivalence (7.4.1); it is the backbone's `OrthonormalBasis.exists_bounds_rpow_one_add_norm_sq`
in the standard basis, with `c₁ = #{α : |α| ≤ k}^{-1/2}` and `c₂ = (1 + d)^{k/2}`. -/
theorem exercise_7_4_2 (d k : ℕ) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ ξ : EuclideanSpace ℝ (Fin d),
        c₁ * Real.sqrt (∑ α : MultiIndexLE (Fin d) k, |xiPow α.1 ξ| ^ 2)
            ≤ (1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2)
          ∧ (1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2)
            ≤ c₂ * Real.sqrt (∑ α : MultiIndexLE (Fin d) k, |xiPow α.1 ξ| ^ 2) := by
  have hS : ∀ ξ : EuclideanSpace ℝ (Fin d),
      (∑ α : MultiIndexLE (Fin d) k, |xiPow α.1 ξ| ^ 2)
        = (EuclideanSpace.basisFun (Fin d) ℝ).sumSqCoordMonomial k ξ := fun ξ ↦
    Finset.sum_congr rfl fun α _ ↦ by rw [sq_abs, xiPow_eq_coordMonomial]
  simpa only [hS] using
    (EuclideanSpace.basisFun (Fin d) ℝ).exists_bounds_rpow_one_add_norm_sq k

/-- **(7.4.1)** for the complex-valued functions that §7.4 allows throughout: there are
`c₁, c₂ > 0` with

`c₁ ‖v‖_{H^k(ℝ^d)} ≤ ‖(1 + |ξ|²)^{k/2} ℱv‖_{L²(ℝ^d)} ≤ c₂ ‖v‖_{H^k(ℝ^d)}`

for every `v ∈ H^k(ℝ^d)`, the left-hand norm being the one Definition 7.2.2 displays,
`[∑_{|α| ≤ k} ‖∂^α v‖²_{L²}]^{1/2}`, which is the norm of
`SobolevMultiIndex ℂ (stdBasis d) k 2 ⊤ volume` by `SobolevMultiIndex.norm_eq_sum`
(`definition_7_2_2_multiIndex_norm` is that display for real-valued functions). The hypothesis is
that the family `w` consists of the weak derivatives `∂^α v` of Definition 7.1.3, which — `v` and
each `w α` lying in `L²(ℝ^d)` — is exactly membership of `H^k(ℝ^d)`.

The proof is Plancherel applied to each `∂^α v`, whose Fourier transform is `(2πi ξ)^α ℱv`,
followed by the symbol inequality of Exercise 7.4.2: the backbone's
`OrthonormalBasis.exists_norm_equiv_eLpNorm_symbol_mul_fourier` in the standard basis. The
constants are `c₁ = ((2π)^{2k} #{α : |α| ≤ k})^{-1/2}` and `c₂ = (1 + d)^{k/2}`. -/
theorem equation_7_4_1_complex (d k : ℕ) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ (v : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
        (w : MultiIndexLE (Fin d) k → Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))),
        (∀ α : MultiIndexLE (Fin d) k, HasWeakIteratedLineDerivOn
            (multiIndexTuple (stdBasis d) α.1) (v : EuclideanSpace ℝ (Fin d) → ℂ)
            (w α : EuclideanSpace ℝ (Fin d) → ℂ) ⊤ volume) →
        c₁ * (∑ α, ‖w α‖ ^ 2) ^ ((1 : ℝ) / 2)
            ≤ (eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (𝓕 v) ξ) 2
                volume).toReal
          ∧ (eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (𝓕 v) ξ) 2
                volume).toReal ≤ c₂ * (∑ α, ‖w α‖ ^ 2) ^ ((1 : ℝ) / 2) :=
  (EuclideanSpace.basisFun (Fin d) ℝ).exists_norm_equiv_eLpNorm_symbol_mul_fourier k

/-- **(7.4.1)**: there are `c₁, c₂ > 0` with

`c₁ ‖v‖_{H^k(ℝ^d)} ≤ ‖(1 + |ξ|²)^{k/2} ℱv‖_{L²(ℝ^d)} ≤ c₂ ‖v‖_{H^k(ℝ^d)}`

for every real `v ∈ H^k(ℝ^d)`, so that `‖(1 + |ξ|²)^{k/2} ℱv‖_{L²}` is a norm on `H^k(ℝ^d)`
equivalent to the canonical one. The left-hand norm is the one Definition 7.2.2 displays,
`[∑_{|α| ≤ k} ‖∂^α v‖²_{L²}]^{1/2}`, which is the norm of
`SobolevMultiIndex ℝ (stdBasis d) k 2 ⊤ volume` by `definition_7_2_2_multiIndex_norm`; the
hypothesis is that `w α` is the weak `∂^α v` of Definition 7.1.3 for every `|α| ≤ k`, which — `v`
and each `w α` lying in `L²(ℝ^d)` — is membership of `H^k(ℝ^d)`.

As in `theorem_7_4_1`, `ℱv` is read as the Fourier transform of the complexification of `v`;
`equation_7_4_1_complex` is the statement for the complex-valued functions §7.4 allows
throughout. -/
theorem equation_7_4_1 (d k : ℕ) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ (v : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
        (w : MultiIndexLE (Fin d) k → Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))),
        (∀ α : MultiIndexLE (Fin d) k, definition_7_1_3_multiIndex α.1
            (v : EuclideanSpace ℝ (Fin d) → ℝ) (w α : EuclideanSpace ℝ (Fin d) → ℝ) ⊤) →
        c₁ * (∑ α, ‖w α‖ ^ 2) ^ ((1 : ℝ) / 2)
            ≤ (eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ)
                * (𝓕 (Complex.ofRealCLM.compLp v)) ξ) 2 volume).toReal
          ∧ (eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ)
                * (𝓕 (Complex.ofRealCLM.compLp v)) ξ) 2 volume).toReal
            ≤ c₂ * (∑ α, ‖w α‖ ^ 2) ^ ((1 : ℝ) / 2) := by
  obtain ⟨c₁, c₂, hc₁, hc₂, h⟩ := equation_7_4_1_complex d k
  refine ⟨c₁, c₂, hc₁, hc₂, fun v w hw ↦ ?_⟩
  have hres : ((⊤ : Opens (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d)))
      = Set.univ := rfl
  have hcoe : ∀ f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))),
      (fun x ↦ (((f : EuclideanSpace ℝ (Fin d) → ℝ) x : ℝ) : ℂ))
        =ᵐ[volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin d))) : Set _)]
        ((Complex.ofRealCLM.compLp f : Lp ℂ 2 _) : EuclideanSpace ℝ (Fin d) → ℂ) := by
    intro f
    rw [hres, Measure.restrict_univ]
    filter_upwards [Complex.ofRealCLM.coeFn_compLp f] with x hx using hx.symm
  have key := h (Complex.ofRealCLM.compLp v) (fun α ↦ Complex.ofRealCLM.compLp (w α)) fun α ↦
    (HasWeakIteratedLineDerivOn.ofReal_iff.1 (hw α)).congr_ae (hcoe v) (hcoe (w α))
  simpa only [Lp.norm_ofRealCLM_compLp] using key

end NormEquivalence

/-! ### Example 7.4.2: `H^k(Ω) ↪ C(Ω̄)` for `k > d/2` -/

section Embedding

variable {d : ℕ}

/-- **Example 7.4.2**: on a bounded extension domain `Ω ⊆ ℝ^{d+1}` (the book's Lipschitz domain)
with `k > (d+1)/2`, `H^k(Ω) ↪ C(Ω̄)`: there is a bounded linear `ι : H^k(Ω) → C(Ω̄)` sending `v`
to the restriction of a continuous representative of `v`, and
`‖v‖_{C(Ω̄)} ≤ c ‖v‖_{H^k(Ω)}` (7.4.3) for all `v ∈ H^k(Ω)`; `ι` is even compact.

The book's proof is by the Fourier transform on `ℝ^d` (Step 1, the Cauchy–Schwarz inequality
against `∫ (1 + |ξ|²)^{−k} dξ < ∞`), the density of Theorem 7.3.4 (Step 2) and the extension
operator of Theorem 7.3.5 at order `k` (Step 3). The formalization is the Sobolev embedding
`theorem_7_3_8_c` instead — `W^{k,2}(Ω) ↪ W^{1,r}(Ω)` for an `r > d + 1` and Morrey's theorem
through the order-one extension operator
(`SobolevEuclidean.exists_isCompactEmbedding_toContinuousMap_of_order`) — the shorter
route, and it also gives the compactness of `ι`, which the book's route does not. Step 3 at
order `k` is `theorem_7_3_5_order`; Stein's universal operator is not formalized.
`H^k(Ω) = W^{k,2}(Ω)` is the space of Definition 7.2.2 in the book's own indexing. -/
theorem example_7_4_2 {k : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : IsSobolevExtensionDomainAll (d + 1) Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hk : ((d + 1 : ℕ) : ℝ) / 2 < k) :
    haveI : CompactSpace (closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
      isCompact_iff_compactSpace.1 hb.isCompact_closure
    ∃ ι : SobolevMultiIndex ℝ (stdBasis (d + 1)) k 2 Ω volume →L[ℝ]
        C(closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), ℝ),
      (∀ v, ∃ v' : EuclideanSpace ℝ (Fin (d + 1)) → ℝ, Continuous v' ∧
        SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] v' ∧
        ∀ x, ι v x = v' x) ∧
      definition_7_3_6 ι.toLinearMap ∧ ∃ c : ℝ, ∀ v, ‖ι v‖ ≤ c * ‖v‖ := by
  have : CompactSpace (closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    isCompact_iff_compactSpace.1 hb.isCompact_closure
  have hk1 : 1 ≤ k := by
    have h1 : (0 : ℝ) < (d + 1 : ℕ) / 2 := by positivity
    exact_mod_cast h1.trans hk
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hk' : ((d + 1 : ℕ) : ℝ) / ((2 : ℝ≥0) : ℝ) < ((k + 1 : ℕ) : ℝ) := by
    rw [NNReal.coe_ofNat]
    exact hk
  have : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩
  have h := SobolevEuclidean.exists_isCompactEmbedding_toContinuousMap_of_order (p := 2) k hΩ
    (Or.inr (by norm_num)) hk' (K := closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    subset_closure
  obtain ⟨ι, hι, hc⟩ := h
  exact ⟨ι, hι, hc.toIsContinuousEmbedding, ‖ι‖, ι.le_opNorm⟩

end Embedding

/-! ### Example 7.4.3 on the whole space: the interpolation inequality (7.4.4) -/

section Interpolation

variable {d : ℕ}

/-- **Example 7.4.3 on the whole space `ℝ^d`, for the complex-valued functions that §7.4 allows**:
for `d ≥ 1` there is `c ≥ 0` such that every `v ∈ H^d(ℝ^d)` — `v ∈ L²(ℝ^d)` with weak derivatives
`w α = ∂^α v ∈ L²(ℝ^d)` for `|α| ≤ d`, as in `equation_7_4_1_complex` — has a continuous
representative `v'` with

`‖v'‖_{C(ℝ^d)} ≤ c ‖v‖_{H^d(ℝ^d)}^{1/2} ‖v‖_{L²(ℝ^d)}^{1/2}` (7.4.4),

the `H^d` norm being `(∑_{|α| ≤ d} ‖∂^α v‖²_{L²})^{1/2}` (Definition 7.2.2). The book's proof:
`|v(x)| ≤ ∫ |ℱv|` for the continuous representative
(`exists_continuous_ae_eq_of_integrable_fourier`, `ℱv ∈ L¹` by
`TemperedDistribution.MemSobolev.fourier_memL1`), the Cauchy–Schwarz inequality against the scaled
weight `(1 + λ|ξ|²)^{±d/2}` (`sq_toReal_lintegral_enorm_fourier_le`, with the norm equivalence
(7.4.1) on the Fourier side), and the choice `λ = (‖v‖_{L²}/‖v‖_{H^d})^{2/d}`
(`exists_rpow_neg_half_mul_add_eq`). The domain form on a Lipschitz `Ω` is the open
`example_7_4_3`. -/
theorem example_7_4_3_whole_space_complex (hd : 1 ≤ d) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (v : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
      (w : MultiIndexLE (Fin d) d → Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))),
      (∀ α : MultiIndexLE (Fin d) d, HasWeakIteratedLineDerivOn
          (multiIndexTuple (stdBasis d) α.1) (v : EuclideanSpace ℝ (Fin d) → ℂ)
          (w α : EuclideanSpace ℝ (Fin d) → ℂ) ⊤ volume) →
      ∃ v' : EuclideanSpace ℝ (Fin d) → ℂ, Continuous v' ∧
        (v : EuclideanSpace ℝ (Fin d) → ℂ) =ᵐ[volume] v' ∧
        ∀ x, ‖v' x‖ ≤ c * ((∑ α, ‖w α‖ ^ 2) ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / 2)
          * ‖v‖ ^ ((1 : ℝ) / 2) := by
  obtain ⟨c₁, c₂, -, hc₂, hEq⟩ := equation_7_4_1_complex d d
  obtain ⟨I, hI⟩ : ∃ I : ℝ, I = (∫⁻ ξ : EuclideanSpace ℝ (Fin d),
      ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)))).toReal := ⟨_, rfl⟩
  have hI0 : 0 ≤ I := hI ▸ ENNReal.toReal_nonneg
  refine ⟨Real.sqrt (2 ^ (d + 1) * I * c₂), Real.sqrt_nonneg _, fun v w hw ↦ ?_⟩
  -- membership in `H^d` and integrability of the Fourier transform
  have hres : ((⊤ : Opens (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d)))
      = Set.univ := rfl
  have hv : MemSobolevMultiIndex (stdBasis d) (v : EuclideanSpace ℝ (Fin d) → ℂ) d 2 ⊤ volume := by
    refine ⟨?_, fun α hα ↦ ⟨(w ⟨α, hα⟩ : EuclideanSpace ℝ (Fin d) → ℂ), hw ⟨α, hα⟩, ?_⟩⟩
    · rw [hres, Measure.restrict_univ]; exact Lp.memLp v
    · rw [hres, Measure.restrict_univ]; exact Lp.memLp (w ⟨α, hα⟩)
  have hF : MemLp (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((d : ℝ) / 2) : ℝ) : ℂ) * (𝓕 v) ξ) 2 volume :=
    (theorem_7_4_1_complex v).1 hv
  have hMS : MemSobolev (d : ℝ) 2 (v : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) :=
    (equation_7_4_2 (by positivity) v).2 hF
  obtain ⟨g, hg⟩ := hMS.fourier_memL1 (by
    rw [finrank_euclideanSpace_fin]
    exact_mod_cast (by omega : d < 2 * d))
  rw [Lp.fourier_toTemperedDistribution_eq] at hg
  have hgae := ae_eq_of_toTemperedDistribution_eq _ g hg
  have hFint : Integrable ((𝓕 v : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
      : EuclideanSpace ℝ (Fin d) → ℂ) := (L1.integrable_coeFn g).congr hgae.symm
  -- the continuous representative
  obtain ⟨v', hv'c, hv'ae, hv'b⟩ := exists_continuous_ae_eq_of_integrable_fourier v hFint
  refine ⟨v', hv'c, hv'ae, fun x ↦ ?_⟩
  obtain ⟨J, hJ⟩ : ∃ J : ℝ, J = (∫⁻ ξ, ‖(𝓕 v : Lp ℂ 2 (volume : Measure _)) ξ‖ₑ).toReal := ⟨_, rfl⟩
  have hJreal : ∫ ξ, ‖(𝓕 v : Lp ℂ 2 (volume : Measure _)) ξ‖ = J := by
    rw [hJ]; exact integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable _)
  have hJ0 : 0 ≤ J := hJ ▸ ENNReal.toReal_nonneg
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = (eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((d : ℝ) / 2) : ℝ) : ℂ)
      * (𝓕 v) ξ) 2 volume).toReal := ⟨_, rfl⟩
  have hNle : N ≤ c₂ * (∑ α, ‖w α‖ ^ 2) ^ ((1 : ℝ) / 2) := hN ▸ (hEq v w hw).2
  have hvN : ‖v‖ ≤ N := hN ▸ norm_le_toReal_eLpNorm_symbol_mul_fourier (Nat.cast_nonneg d) v hF
  have hSnn : (0 : ℝ) ≤ ∑ α, ‖w α‖ ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hS : (0 : ℝ) ≤ (∑ α, ‖w α‖ ^ 2) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hSnn _
  -- the case `v = 0`
  rcases eq_or_lt_of_le (norm_nonneg v) with hv0 | hv0
  · have hF0 : (fun ξ ↦ ‖(𝓕 v : Lp ℂ 2 (volume : Measure _)) ξ‖) =ᵐ[volume] 0 := by
      have : 𝓕 v = 0 := by
        rw [← norm_eq_zero, Lp.norm_fourier_eq, ← hv0]
      rw [this]
      filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure _))] with ξ hξ
      simp only [hξ, Pi.zero_apply, norm_zero]
    calc ‖v' x‖ ≤ ∫ ξ, ‖(𝓕 v : Lp ℂ 2 (volume : Measure _)) ξ‖ := hv'b x
      _ = 0 := by rw [integral_congr_ae hF0]; simp
      _ ≤ _ := by positivity
  -- the case `v ≠ 0`: the scaling
  have ha : 0 < ‖v‖ ^ 2 := by positivity
  have hb : 0 < (c₂ * (∑ α, ‖w α‖ ^ 2) ^ ((1 : ℝ) / 2)) ^ 2 := by
    exact pow_pos (hv0.trans_le (hvN.trans hNle)) 2
  obtain ⟨l, hl, hopt⟩ := exists_rpow_neg_half_mul_add_eq (by omega : d ≠ 0) ha hb
  have hmain := sq_toReal_lintegral_enorm_fourier_le (k := d)
    (by rw [finrank_euclideanSpace_fin]; omega) v hF hl
  rw [finrank_euclideanSpace_fin, ← hJ, ← hI, ← hN] at hmain
  have hmain' : J ^ 2 ≤ 2 ^ (d + 1) * I * c₂ * ‖v‖ * (∑ α, ‖w α‖ ^ 2) ^ ((1 : ℝ) / 2) := by
    have hld : 0 ≤ l ^ (-(d : ℝ) / 2) := Real.rpow_nonneg hl.le _
    have hN0 : 0 ≤ N := (norm_nonneg v).trans hvN
    calc J ^ 2 ≤ l ^ (-(d : ℝ) / 2) * I * (2 ^ d * (‖v‖ ^ 2 + l ^ d * N ^ 2)) := hmain
      _ ≤ l ^ (-(d : ℝ) / 2) * I * (2 ^ d
          * (‖v‖ ^ 2 + l ^ d * (c₂ * (∑ α, ‖w α‖ ^ 2) ^ ((1 : ℝ) / 2)) ^ 2)) := by gcongr
      _ = 2 ^ d * I * (l ^ (-(d : ℝ) / 2)
          * (‖v‖ ^ 2 + l ^ d * (c₂ * (∑ α, ‖w α‖ ^ 2) ^ ((1 : ℝ) / 2)) ^ 2)) := by ring
      _ = 2 ^ d * I * (2 * Real.sqrt (‖v‖ ^ 2)
          * Real.sqrt ((c₂ * (∑ α, ‖w α‖ ^ 2) ^ ((1 : ℝ) / 2)) ^ 2)) := by rw [hopt]
      _ = 2 ^ (d + 1) * I * c₂ * ‖v‖ * (∑ α, ‖w α‖ ^ 2) ^ ((1 : ℝ) / 2) := by
          rw [Real.sqrt_sq (norm_nonneg v), Real.sqrt_sq (mul_nonneg hc₂.le hS)]
          ring
  calc ‖v' x‖ ≤ J := hJreal ▸ hv'b x
    _ = Real.sqrt (J ^ 2) := (Real.sqrt_sq hJ0).symm
    _ ≤ Real.sqrt (2 ^ (d + 1) * I * c₂ * ‖v‖ * (∑ α, ‖w α‖ ^ 2) ^ ((1 : ℝ) / 2)) :=
        Real.sqrt_le_sqrt hmain'
    _ = Real.sqrt (2 ^ (d + 1) * I * c₂) * ((∑ α, ‖w α‖ ^ 2) ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / 2)
          * ‖v‖ ^ ((1 : ℝ) / 2) := by
        have hc0 : 0 ≤ 2 ^ (d + 1) * I * c₂ := mul_nonneg (mul_nonneg (by positivity) hI0) hc₂.le
        rw [Real.sqrt_mul (mul_nonneg hc0 (norm_nonneg v)), Real.sqrt_mul hc0]
        simp only [Real.sqrt_eq_rpow]
        ring

/-- **Example 7.4.3 on the whole space `ℝ^d`**: for `d ≥ 1` there is `c ≥ 0` such that every real
`v ∈ H^d(ℝ^d)` — `v ∈ L²(ℝ^d)` with weak derivatives `w α = ∂^α v ∈ L²(ℝ^d)` (Definition 7.1.3)
for `|α| ≤ d` — has a continuous representative `v'` with

`‖v'‖_{C(ℝ^d)} ≤ c ‖v‖_{H^d(ℝ^d)}^{1/2} ‖v‖_{L²(ℝ^d)}^{1/2}` (7.4.4),

the `H^d` norm being `(∑_{|α| ≤ d} ‖∂^α v‖²_{L²})^{1/2}` of Definition 7.2.2. This is the
whole-space case `Ω = ℝ^d` of the book's Example 7.4.3, which the book's proof reduces to;
`example_7_4_3_whole_space_complex` is the statement for the complex-valued functions that §7.4
allows, and the domain form on a Lipschitz `Ω` is the open `example_7_4_3`. -/
theorem example_7_4_3_whole_space (hd : 1 ≤ d) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (v : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
      (w : MultiIndexLE (Fin d) d → Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))),
      (∀ α : MultiIndexLE (Fin d) d, definition_7_1_3_multiIndex α.1
          (v : EuclideanSpace ℝ (Fin d) → ℝ) (w α : EuclideanSpace ℝ (Fin d) → ℝ) ⊤) →
      ∃ v' : EuclideanSpace ℝ (Fin d) → ℝ, Continuous v' ∧
        (v : EuclideanSpace ℝ (Fin d) → ℝ) =ᵐ[volume] v' ∧
        ∀ x, |v' x| ≤ c * ((∑ α, ‖w α‖ ^ 2) ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / 2)
          * ‖v‖ ^ ((1 : ℝ) / 2) := by
  obtain ⟨c, hc0, h⟩ := example_7_4_3_whole_space_complex hd
  refine ⟨c, hc0, fun v w hw ↦ ?_⟩
  have hres : ((⊤ : Opens (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d)))
      = Set.univ := rfl
  have hcoe : ∀ f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))),
      (fun x ↦ (((f : EuclideanSpace ℝ (Fin d) → ℝ) x : ℝ) : ℂ))
        =ᵐ[volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin d))) : Set _)]
        ((Complex.ofRealCLM.compLp f : Lp ℂ 2 _) : EuclideanSpace ℝ (Fin d) → ℂ) := by
    intro f
    rw [hres, Measure.restrict_univ]
    filter_upwards [Complex.ofRealCLM.coeFn_compLp f] with x hx using hx.symm
  obtain ⟨v', hv'c, hv'ae, hv'b⟩ := h (Complex.ofRealCLM.compLp v)
    (fun α ↦ Complex.ofRealCLM.compLp (w α)) fun α ↦
      (HasWeakIteratedLineDerivOn.ofReal_iff.1 (hw α)).congr_ae (hcoe v) (hcoe (w α))
  refine ⟨fun x ↦ (v' x).re, Complex.continuous_re.comp hv'c, ?_, fun x ↦ ?_⟩
  · have h1 := hcoe v
    rw [hres, Measure.restrict_univ] at h1
    filter_upwards [h1, hv'ae] with x hx hx'
    rw [← hx', ← hx, Complex.ofReal_re]
  · calc |(v' x).re| ≤ ‖v' x‖ := Complex.abs_re_le_norm _
      _ ≤ _ := hv'b x
      _ = _ := by simp only [Lp.norm_ofRealCLM_compLp]

/-! ### Example 7.4.3 on a domain -/

/-- **The `L²(ℝ^N)` data of an element of `W^{N,2}(ℝ^N)`**: the function and the weak derivatives
`∂^α`, `|α| ≤ N`, of `u ∈ W^{N,2}(ℝ^N)` as elements of `L²(ℝ^N)` for the unrestricted measure,
with the weak-derivative relations of Definition 7.1.3 and the two norms —
`(∑_{|α| ≤ N} ‖∂^α u‖²)^{1/2} = ‖u‖_{H^N}` (Definition 7.2.2) and `‖u‖_{L²}`. The whole point is
the passage from `volume.restrict ↑(⊤ : Opens _)`, the measure the typed space carries on `ℝ^N`,
to `volume`, the measure `example_7_4_3_whole_space` is stated for. -/
private theorem exists_lp_data_of_top {N k : ℕ}
    (u : SobolevMultiIndex ℝ (stdBasis N) k 2 (⊤ : Opens (EuclideanSpace ℝ (Fin N))) volume) :
    ∃ (V : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin N))))
      (W : MultiIndexLE (Fin N) k → Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin N)))),
      (V : EuclideanSpace ℝ (Fin N) → ℝ) =ᵐ[volume] SobolevMultiIndex.fn u ∧
      (∀ α : MultiIndexLE (Fin N) k, definition_7_1_3_multiIndex α.1
        (V : EuclideanSpace ℝ (Fin N) → ℝ) (W α : EuclideanSpace ℝ (Fin N) → ℝ) ⊤) ∧
      (∑ α, ‖W α‖ ^ 2) ^ ((1 : ℝ) / 2) = ‖u‖ ∧
      ‖V‖ = (eLpNorm (SobolevMultiIndex.fn u) 2 volume).toReal := by
  have hres : ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) : Set (EuclideanSpace ℝ (Fin N)))
      = Set.univ := rfl
  have hμ : (volume : Measure (EuclideanSpace ℝ (Fin N))).restrict
      ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) : Set (EuclideanSpace ℝ (Fin N))) = volume := by
    rw [hres, Measure.restrict_univ]
  -- the weak derivatives, as functions: naming them frees the rewrite `hμ` from the dependence
  -- of the type of `SobolevMultiIndex.weakDeriv u α` on the measure
  obtain ⟨g, hg⟩ : ∃ g : MultiIndexLE (Fin N) k → EuclideanSpace ℝ (Fin N) → ℝ,
      ∀ α, g α = (SobolevMultiIndex.weakDeriv u α : EuclideanSpace ℝ (Fin N) → ℝ) :=
    ⟨_, fun _ ↦ rfl⟩
  have hmemV : MemLp (SobolevMultiIndex.fn u) 2 (volume : Measure (EuclideanSpace ℝ (Fin N))) := by
    have h := SobolevMultiIndex.memLp u
    rwa [hμ] at h
  have hmemW : ∀ α : MultiIndexLE (Fin N) k,
      MemLp (g α) 2 (volume : Measure (EuclideanSpace ℝ (Fin N))) := fun α ↦ by
    have h : MemLp (g α) 2 ((volume : Measure (EuclideanSpace ℝ (Fin N))).restrict
        ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) : Set (EuclideanSpace ℝ (Fin N)))) := by
      rw [hg α]; exact Lp.memLp _
    rwa [hμ] at h
  refine ⟨hmemV.toLp _, fun α ↦ (hmemW α).toLp _, hmemV.coeFn_toLp, fun α ↦ ?_, ?_, ?_⟩
  · refine (SobolevMultiIndex.hasWeakIteratedLineDerivOn u α).congr_ae
      (hmemV.coeFn_toLp.symm.filter_mono (ae_mono Measure.restrict_le_self)) ?_
    refine Filter.EventuallyEq.filter_mono ?_ (ae_mono Measure.restrict_le_self)
    rw [← hg α]
    exact (hmemW α).coeFn_toLp.symm
  · rw [SobolevMultiIndex.norm_eq_sum (by simp) u]
    have h2 : ((2 : ℝ≥0∞)).toReal = 2 := by simp
    rw [h2]
    congr 1
    refine Finset.sum_congr rfl fun α _ ↦ ?_
    rw [Real.rpow_two, Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (hmemW α).coeFn_toLp, ← hg α, hμ]
  · rw [Lp.norm_def, eLpNorm_congr_ae hmemV.coeFn_toLp]

/-- **Example 7.4.3 on the whole space, in the typed Sobolev space**: `example_7_4_3_whole_space`
restated for `u ∈ W^{N,2}(ℝ^N) = H^N(ℝ^N)` of `definition_7_2_2_multiIndex`, with `‖u‖` the norm
of Definition 7.2.2 and `‖u‖_{L²}` read as `(eLpNorm (fn u) 2 volume).toReal`. -/
private theorem example_7_4_3_whole_space_typed {N : ℕ} (hN : 1 ≤ N) :
    ∃ c : ℝ, 0 ≤ c ∧
      ∀ u : SobolevMultiIndex ℝ (stdBasis N) N 2 (⊤ : Opens (EuclideanSpace ℝ (Fin N))) volume,
        ∃ u' : EuclideanSpace ℝ (Fin N) → ℝ, Continuous u' ∧
          SobolevMultiIndex.fn u =ᵐ[volume] u' ∧
          ∀ x, |u' x| ≤ c * ‖u‖ ^ ((1 : ℝ) / 2)
            * (eLpNorm (SobolevMultiIndex.fn u) 2 volume).toReal ^ ((1 : ℝ) / 2) := by
  obtain ⟨c₀, hc₀, hws⟩ := example_7_4_3_whole_space hN
  refine ⟨c₀, hc₀, fun u ↦ ?_⟩
  obtain ⟨V, W, hVfn, hW, hWnorm, hVnorm⟩ := exists_lp_data_of_top u
  obtain ⟨u', hu'c, hu'ae, hu'b⟩ := hws V W hW
  refine ⟨u', hu'c, hVfn.symm.trans hu'ae, fun x ↦ ?_⟩
  have h := hu'b x
  rwa [hWnorm, hVnorm] at h

/-- **Example 7.4.3**: on a bounded `C^{d+1}` domain `Ω ⊆ ℝ^{d+1}` there is a `c ≥ 0` such that
every `v ∈ H^{d+1}(Ω)` has a representative `v'` continuous on all of `ℝ^{d+1}` with

`‖v‖_{C(Ω̄)} ≤ c ‖v‖_{H^{d+1}(Ω)}^{1/2} ‖v‖_{L²(Ω)}^{1/2}` (7.4.4),

in fact `|v'(x)| ≤ c ‖v‖^{1/2} ‖v‖_{L²(Ω)}^{1/2}` at every `x ∈ ℝ^{d+1}`. The `H^{d+1}(Ω)` norm
is the norm of Definition 7.2.2 that the type carries and the `L²(Ω)` norm is
`(eLpNorm (fn v) 2 (volume.restrict Ω)).toReal`; the ambient dimension is written `d + 1`, as in
Definition 7.2.1, so that the book's `d` is `d + 1` here and the order of the Sobolev space is
the dimension.

The book's `Ω` is a Lipschitz domain and its `E` is the universal extension operator of
Theorem 7.3.5, bounded on `H^k` for every `k` at once; here `Ω` is a bounded `C^{d+1}` domain, as
everywhere in this chapter, and `E` is the order-`(d+1)` operator of `theorem_7_3_5_order_lp`,
which is bounded on `H^{d+1}(Ω)` *and* on `L²(Ω)` — the two bounds the argument needs, and no
more. Step 3 of the book's proof is then exactly the calculation here:
`‖v'‖_∞ ≤ c₀ ‖Ev‖_{H^{d+1}}^{1/2} ‖Ev‖_{L²}^{1/2}` and then
`≤ c₀ c_E ‖v‖_{H^{d+1}(Ω)}^{1/2} ‖v‖_{L²(Ω)}^{1/2}`, the first inequality being
`example_7_4_3_whole_space` (Steps 1 and 2, the Fourier route). -/
theorem example_7_4_3 {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : definition_7_2_1 {g | ContDiff ℝ (d + 1 : ℕ) g} Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    ∃ c : ℝ, 0 ≤ c ∧
      ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) (d + 1) 2 Ω volume,
        ∃ v' : EuclideanSpace ℝ (Fin (d + 1)) → ℝ, Continuous v' ∧
          SobolevMultiIndex.fn v
            =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] v' ∧
          ∀ x, |v' x| ≤ c * ‖v‖ ^ ((1 : ℝ) / 2)
            * (eLpNorm (SobolevMultiIndex.fn v) 2
                (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))).toReal
              ^ ((1 : ℝ) / 2) := by
  obtain ⟨c₀, hc₀, hws⟩ := example_7_4_3_whole_space_typed (N := d + 1) (Nat.le_add_left 1 d)
  have hEx := theorem_7_3_5_order_lp (k := d + 1) (p := 2) (Nat.le_add_left 1 d) hΩ hb
  obtain ⟨E, hEae, cE, hEnorm, hElp⟩ := hEx
  have hcE : (0 : ℝ) ≤ max cE 0 := le_max_right _ _
  refine ⟨c₀ * max cE 0, by positivity, fun v ↦ ?_⟩
  have hwv := hws (E v)
  obtain ⟨v', hv'c, hv'ae, hv'b⟩ := hwv
  refine ⟨v', hv'c, (hEae v).symm.trans
    (hv'ae.filter_mono (ae_mono Measure.restrict_le_self)), fun x ↦ ?_⟩
  have hv0 : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
  have hL0 : (0 : ℝ) ≤ (eLpNorm (SobolevMultiIndex.fn v) 2
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))).toReal :=
    ENNReal.toReal_nonneg
  have h1 : ‖E v‖ ≤ max cE 0 * ‖v‖ :=
    (hEnorm v).trans (by gcongr; exact le_max_left _ _)
  have h2 : (eLpNorm (SobolevMultiIndex.fn (E v)) 2 volume).toReal
      ≤ max cE 0 * (eLpNorm (SobolevMultiIndex.fn v) 2
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))).toReal := by
    have hne : ENNReal.ofReal cE * eLpNorm (SobolevMultiIndex.fn v) 2
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (SobolevMultiIndex.memLp v).eLpNorm_ne_top
    refine (ENNReal.toReal_mono hne (hElp v)).trans_eq ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal']
  have hA : (max cE 0) ^ ((1 : ℝ) / 2) * (max cE 0) ^ ((1 : ℝ) / 2) = max cE 0 := by
    rw [← Real.rpow_add' hcE (by norm_num)]
    norm_num
  calc |v' x| ≤ c₀ * ‖E v‖ ^ ((1 : ℝ) / 2)
        * (eLpNorm (SobolevMultiIndex.fn (E v)) 2 volume).toReal ^ ((1 : ℝ) / 2) := hv'b x
    _ ≤ c₀ * (max cE 0 * ‖v‖) ^ ((1 : ℝ) / 2)
        * (max cE 0 * (eLpNorm (SobolevMultiIndex.fn v) 2
            (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))).toReal)
          ^ ((1 : ℝ) / 2) := by
        gcongr
    _ = c₀ * max cE 0 * ‖v‖ ^ ((1 : ℝ) / 2)
        * (eLpNorm (SobolevMultiIndex.fn v) 2
            (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))).toReal
          ^ ((1 : ℝ) / 2) := by
        rw [Real.mul_rpow hcE hv0, Real.mul_rpow hcE hL0]
        calc c₀ * ((max cE 0) ^ ((1 : ℝ) / 2) * ‖v‖ ^ ((1 : ℝ) / 2))
              * ((max cE 0) ^ ((1 : ℝ) / 2) * (eLpNorm (SobolevMultiIndex.fn v) 2
                (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))).toReal
                ^ ((1 : ℝ) / 2))
            = c₀ * ((max cE 0) ^ ((1 : ℝ) / 2) * (max cE 0) ^ ((1 : ℝ) / 2))
              * (‖v‖ ^ ((1 : ℝ) / 2) * (eLpNorm (SobolevMultiIndex.fn v) 2
                (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))).toReal
                ^ ((1 : ℝ) / 2)) := by ring
          _ = c₀ * max cE 0 * ‖v‖ ^ ((1 : ℝ) / 2)
              * (eLpNorm (SobolevMultiIndex.fn v) 2
                (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))).toReal
                ^ ((1 : ℝ) / 2) := by rw [hA]; ring


end Interpolation

end AtkinsonHan.Chapter07
