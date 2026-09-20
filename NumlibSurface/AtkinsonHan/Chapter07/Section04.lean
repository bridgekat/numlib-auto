import Mathlib.Analysis.Distribution.Sobolev
import Numlib.Analysis.Sobolev.Tempered
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
multiplying back by `(1 + |ξ|^2)^{-s/2}`, which is bounded exactly when `s ≥ 0`.

The book's (7.4.1), the *equivalence* of `‖(1 + |ξ|^2)^{k/2} ℱv‖_{L^2}` with the Sobolev norm
`[∑_{|α| ≤ k} ‖∂^α v‖_{L^2}^2]^{1/2}` of Definition 7.2.2, is a separate statement from
Theorem 7.4.1's membership criterion — which goes through Mathlib's
`TemperedDistribution.MemSobolev.fourierMultiplierCLM_of_bounded`, a soft statement about bounded
symbols that carries no constants. It is `equation_7_4_1`, with `equation_7_4_1_complex` its
complex-valued form, and it rests on two things. The first is **Exercise 7.4.2**, the two-sided
symbol inequality `c₁ (∑_{|α| ≤ k} |ξ^α|²)^{1/2} ≤ (1 + |ξ|²)^{k/2} ≤ c₂ (∑_{|α| ≤ k}
|ξ^α|²)^{1/2}`, proved here as `exercise_7_4_2`; the lower bound needs no multinomial expansion,
only the largest coordinate. The second is the Fourier transform of a weak derivative on the whole
space, `ℱ(∂^α v) = (2πiξ)^α ℱv`, which is `fourier_weakDeriv_aeEq` — Mathlib's
`TemperedDistribution.fourier_lineDerivOp_eq` iterated (`fourier_iteratedLineDerivOp_eq`), pushed
onto the `L²` representatives by the injectivity of `MeasureTheory.Lp.toTemperedDistributionCLM`.
Plancherel then turns `∑_{|α| ≤ k} ‖∂^α v‖²_{L²}` into `∫ (∑_{|α| ≤ k} (2π)^{2|α|} |ξ^α|²) |ℱv|²`
and the symbol inequality compares it with `∫ (1 + |ξ|²)^k |ℱv|²`.
`memSobolev_iteratedLineDerivOp` and `memLp_iteratedLineDerivOp` are the derivative side of the
criterion in the Bessel-potential reading, and delegate to the backbone.

The general material supporting (7.4.1) — the symbol of an iterated directional derivative and
the Fourier transform of a weak derivative — lives in `Numlib/Analysis/Sobolev/Tempered`; what
remains here is the bound on the symbol in the standard basis and the equivalence itself.

Example 7.4.2, `H^k(Ω) ↪ C(Ω̄)` for `k > d/2`, is here as `example_7_4_2` on a bounded extension
domain (the book's Lipschitz domain, the `C¹` domains of Definition 7.2.1 included through
`isSobolevExtensionDomainAll_of_definition_7_2_1`), but *not* by the book's route: the book
proves it by the Fourier characterization on `ℝ^d` (Step 1), the density of Theorem 7.3.4
(Step 2) and the extension operator (Step 3); here it is the Sobolev embedding of Theorem 7.3.8 (c)
— Morrey's theorem on `ℝ^d` through the order-one extension operator, in
`Numlib/Analysis/Sobolev/DenyLions.lean` — since the backbone's extension operator exists at
order one only and Step 3 at order `k` is the open `theorem_7_3_5_universal`. Example 7.4.3, the
interpolation inequality `‖v‖_{C(Ω̄)} ≤ c ‖v‖_{H^d}^{1/2} ‖v‖_{L^2}^{1/2}`, stays open for the same
reason; so do Exercises 7.4.3 and 7.4.4.
-/

open FourierTransform LineDeriv MeasureTheory TemperedDistribution TopologicalSpace

open scoped ENNReal NNReal SchwartzMap

namespace AtkinsonHan.Chapter07

section WholeSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### Multiplying an `L^2` function by a symbol -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The symbol `(1 + |ξ|^2)^{s/2}` has temperate growth. -/
private theorem hasTemperateGrowth_symbol (s : ℝ) :
    (fun ξ : E ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop

/-- **Reading the symbol off the `L^2` representative.** If an `L^2` function `w` is, as a tempered
distribution, the product of the symbol `(1 + |ξ|^2)^{s/2}` with an `L^2` function `u`, and
`s ≥ 0`, then `w` is that product almost everywhere. The hypothesis `s ≥ 0` is what makes the
inverse symbol `(1 + |ξ|^2)^{-s/2}` bounded, so that multiplying the identity by it stays inside
`L^2`. -/
private theorem aeEq_of_smulLeftCLM_eq {s : ℝ} (hs : 0 ≤ s) {u w : Lp ℂ 2 (volume : Measure E)}
    (h : smulLeftCLM ℂ (fun ξ : E ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) (u : 𝓢'(E, ℂ)) =
      (w : 𝓢'(E, ℂ))) :
    (w : E → ℂ) =ᵐ[volume] fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * (u : E → ℂ) ξ := by
  set g : E → ℂ := fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) with hgdef
  set g' : E → ℂ := fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ) with hg'def
  have hpos : ∀ ξ : E, (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := fun ξ ↦ by positivity
  have hg : g.HasTemperateGrowth := hasTemperateGrowth_symbol s
  have hg' : g'.HasTemperateGrowth := hasTemperateGrowth_symbol (-s)
  have hmul : ∀ ξ : E, g ξ * g' ξ = 1 := by
    intro ξ
    simp only [hgdef, hg'def, ← Complex.ofReal_mul, ← Real.rpow_add (hpos ξ)]
    rw [show s / 2 + -s / 2 = (0 : ℝ) by ring, Real.rpow_zero, Complex.ofReal_one]
  have hbdd : ∀ ξ : E, ‖g' ξ‖ ≤ 1 := by
    intro ξ
    simp only [hg'def, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (hpos ξ).le _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [norm_nonneg ξ]) (by linarith)
  have hb : MemLp (fun ξ ↦ g' ξ * (w : E → ℂ) ξ) 2 (volume : Measure E) := by
    refine (Lp.memLp w).mono (hg'.1.continuous.aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable w)) ?_
    filter_upwards with ξ
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hbdd ξ)
  have hu : (hb.toLp _ : 𝓢'(E, ℂ)) = (u : 𝓢'(E, ℂ)) := by
    rw [toTemperedDistribution_eq_smulLeftCLM hg' hb.coeFn_toLp, ← h,
      smulLeftCLM_smulLeftCLM_apply hg hg', show g * g' = fun _ : E ↦ (1 : ℂ) from funext hmul,
      smulLeftCLM_const, one_smul]
  have hinj : Function.Injective (Lp.toTemperedDistributionCLM ℂ (volume : Measure E) 2) :=
    LinearMap.ker_eq_bot.1 Lp.ker_toTemperedDistributionCLM_eq_bot
  have hueq : hb.toLp _ = u := hinj hu
  have huae : (u : E → ℂ) =ᵐ[volume] fun ξ ↦ g' ξ * (w : E → ℂ) ξ := by
    rw [← hueq]; exact hb.coeFn_toLp
  filter_upwards [huae] with ξ hξ
  rw [hξ, ← mul_assoc, hmul ξ, one_mul]

/-! ### The Fourier characterization -/

/-- **The Fourier characterization of `H^s(ℝ^d)` for `s ≥ 0`**: an `L^2` function `v` lies in the
Sobolev space of order `s` exactly when `(1 + |ξ|^2)^{s/2} ℱv` lies in `L^2`, where `ℱv` is the
`L^2` Fourier transform of `v`.

This is `TemperedDistribution.memSobolev_iff_exists_smulLeftCLM_fourier` with the multiplication by
the symbol made concrete: Mathlib states it as an equality of tempered distributions, and here the
`L^2` representative is identified pointwise almost everywhere, which is what the book displays. -/
theorem memSobolev_two_iff_memLp_symbol_mul_fourier {s : ℝ} (hs : 0 ≤ s)
    (v : Lp ℂ 2 (volume : Measure E)) :
    MemSobolev s 2 (v : 𝓢'(E, ℂ)) ↔
      MemLp (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * (𝓕 v) ξ) 2
        (volume : Measure E) := by
  rw [memSobolev_iff_exists_smulLeftCLM_fourier, Lp.fourier_toTemperedDistribution_eq]
  refine ⟨fun ⟨w, hw⟩ ↦ (Lp.memLp w).ae_eq (aeEq_of_smulLeftCLM_eq hs hw), fun hm ↦ ⟨hm.toLp _, ?_⟩⟩
  exact (toTemperedDistribution_eq_smulLeftCLM (hasTemperateGrowth_symbol s) hm.coeFn_toLp).symm

/-- **The Fourier transform of the Bessel potential.** If the Bessel potential of order `s ≥ 0` of
an `L^2` function `v` is the `L^2` function `w`, then `ℱw = (1 + |ξ|^2)^{s/2} ℱv` almost
everywhere. -/
theorem fourier_aeEq_symbol_mul_fourier_of_besselPotential_eq {s : ℝ} (hs : 0 ≤ s)
    {v w : Lp ℂ 2 (volume : Measure E)}
    (hw : besselPotential E ℂ s (v : 𝓢'(E, ℂ)) = (w : 𝓢'(E, ℂ))) :
    ((𝓕 w : Lp ℂ 2 (volume : Measure E)) : E → ℂ) =ᵐ[volume]
      fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * (𝓕 v) ξ := by
  refine aeEq_of_smulLeftCLM_eq hs ?_
  rw [← Lp.fourier_toTemperedDistribution_eq, ← Lp.fourier_toTemperedDistribution_eq, ← hw,
    fourier_besselPotential_eq_smulLeftCLM_fourier_apply]

/-! ### Iterated derivatives -/

/-- **The directional derivatives of a Sobolev distribution.** If `f ∈ H^s(ℝ^d)` then the iterated
directional derivative `∂_{m_1} ⋯ ∂_{m_n} f` lies in `H^{s-n}(ℝ^d)`: Mathlib's
`TemperedDistribution.MemSobolev.lineDerivOp`, iterated, which is the backbone
`TemperedDistribution.MemSobolev.iteratedLineDerivOp`. -/
theorem memSobolev_iteratedLineDerivOp {s : ℝ} {f : 𝓢'(E, ℂ)} (hf : MemSobolev s 2 f) :
    ∀ (n : ℕ) (m : Fin n → E), MemSobolev (s - n) 2 (∂^{m} f) :=
  hf.iteratedLineDerivOp

/-- **The derivatives of order at most `k` of an element of `H^k(ℝ^d)` are `L^2` functions.** This
is the half of Theorem 7.4.1 that Mathlib's Bessel-potential Sobolev space gives directly; that
these distributional derivatives are the weak derivatives of Definition 7.1.3, and that the
converse holds, is the content of `theorem_7_4_1`. -/
theorem memLp_iteratedLineDerivOp {k n : ℕ} (hn : n ≤ k) {f : 𝓢'(E, ℂ)}
    (hf : MemSobolev (k : ℝ) 2 f) (m : Fin n → E) :
    ∃ w : Lp ℂ 2 (volume : Measure E), (∂^{m} f) = (w : 𝓢'(E, ℂ)) :=
  memSobolev_zero_iff.1 <| (memSobolev_iteratedLineDerivOp hf n m).mono <| by
    have : (n : ℝ) ≤ (k : ℝ) := by exact_mod_cast hn
    linarith

end WholeSpace

/-! ### The Fourier definition (7.4.2) of `H^s(ℝ^d)` -/

variable {d : ℕ}

/-- **(7.4.2)**, the definition of `H^s(ℝ^d)` by the Fourier condition: for `v ∈ L^2(ℝ^d)` and a
real `s ≥ 0`, `(1 + |ξ|^2)^{s/2} ℱv` lies in `L^2(ℝ^d)` exactly when `v` lies in `H^s(ℝ^d)`.

`H^s(ℝ^d)` is read here as `TemperedDistribution.MemSobolev s 2`, the Bessel potential space: the
distributions whose Bessel potential of order `s` is an `L^2` function. At `s = 0` this is `L^2`
itself, by `TemperedDistribution.memSobolev_zero_iff`. This is *not* Theorem 7.4.1, whose left-hand
side is the `W^{k,2}(ℝ^d)` of `definition_7_2_2_multiIndex`, cut out by the weak derivatives; that
theorem is `theorem_7_4_1`, and it is this display composed with the bridge of
`Numlib/Analysis/Sobolev/Tempered.lean`. -/
theorem equation_7_4_2 {s : ℝ} (hs : 0 ≤ s)
    (v : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    MemSobolev s 2 (v : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) ↔
      MemLp (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * (𝓕 v) ξ) 2 volume :=
  memSobolev_two_iff_memLp_symbol_mul_fourier hs v

/-- **The norm that goes with (7.4.2)**: for `v ∈ L^2(ℝ^d)` and `s ≥ 0`, if the Bessel potential of
order `s` of `v` is the `L^2` function `w` — so that `‖w‖_{L^2}` is the `H^s(ℝ^d)` norm of `v` in
the Bessel-potential reading — then

`‖w‖_{L^2(ℝ^d)} = ‖(1 + |ξ|^2)^{s/2} ℱv‖_{L^2(ℝ^d)}`,

by Plancherel. This is not the book's (7.4.1), which is the *equivalence* of the right-hand side
with the Sobolev norm `[∑_{|α| ≤ k} ‖∂^α v‖_{L^2}^2]^{1/2}` of Definition 7.2.2 and is the open
node `equation_7_4_1`. -/
theorem equation_7_4_2_norm {s : ℝ} (hs : 0 ≤ s)
    {v w : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))}
    (hw : besselPotential (EuclideanSpace ℝ (Fin d)) ℂ s (v : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) =
      (w : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ))) :
    ‖w‖ =
      (eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * (𝓕 v) ξ) 2 volume).toReal := by
  rw [← Lp.norm_fourier_eq w, Lp.norm_def]
  exact congrArg ENNReal.toReal
    (eLpNorm_congr_ae (fourier_aeEq_symbol_mul_fourier_of_besselPotential_eq hs hw))

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

section SymbolBounds

variable {d k : ℕ}

/-- The monomial `ξ^α = ∏_i ξ_i^{α_i}` of the multi-index `α`. -/
def xiPow (α : Fin d → ℕ) (ξ : EuclideanSpace ℝ (Fin d)) : ℝ := ∏ i, ξ i ^ α i

/-- `ξ^α` is continuous in `ξ`. -/
theorem continuous_xiPow (α : Fin d → ℕ) :
    Continuous (fun ξ : EuclideanSpace ℝ (Fin d) ↦ xiPow α ξ) :=
  continuous_finsetProd _ fun i _ ↦ ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous).pow _

/-- `|ξ^α|² ≤ (1 + |ξ|²)^{|α|}`, because every coordinate is bounded by the norm. -/
theorem sq_xiPow_le (α : Fin d → ℕ) (ξ : EuclideanSpace ℝ (Fin d)) :
    xiPow α ξ ^ 2 ≤ (1 + ‖ξ‖ ^ 2) ^ (∑ i, α i) := by
  rw [xiPow, ← Finset.prod_pow, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod₀ (fun i _ ↦ by positivity) fun i _ ↦ ?_
  rw [← pow_mul, mul_comm (α i) 2, pow_mul]
  refine pow_le_pow_left₀ (by positivity) ?_ _
  have := abs_apply_le_norm ξ i
  nlinarith [abs_nonneg (ξ i), sq_abs (ξ i), norm_nonneg ξ]

/-- `|ξ^α|² ≤ (1 + |ξ|²)^k` for `|α| ≤ k`. -/
theorem sq_xiPow_le_pow {α : Fin d → ℕ} (hα : ∑ i, α i ≤ k) (ξ : EuclideanSpace ℝ (Fin d)) :
    xiPow α ξ ^ 2 ≤ (1 + ‖ξ‖ ^ 2) ^ k :=
  (sq_xiPow_le α ξ).trans (pow_le_pow_right₀ (by nlinarith [norm_nonneg ξ]) hα)

/-- `(x ^ (k/2))² = x^k` for `x ≥ 0`. -/
theorem sq_rpow_half_natCast {x : ℝ} (hx : 0 ≤ x) (k : ℕ) : (x ^ ((k : ℝ) / 2)) ^ 2 = x ^ k := by
  rw [← Real.rpow_natCast (x ^ ((k : ℝ) / 2)) 2, ← Real.rpow_mul hx, div_mul_eq_mul_div,
    mul_comm, mul_div_assoc, show ((2 : ℕ) : ℝ) * ((k : ℝ) / 2) = ((k : ℕ) : ℝ) by
      push_cast; ring, Real.rpow_natCast]

/-- `x ^ (k/2) = √(x^k)` for `x ≥ 0`. -/
theorem rpow_half_eq_sqrt_pow {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    x ^ ((k : ℝ) / 2) = Real.sqrt (x ^ k) := by
  rw [← sq_rpow_half_natCast hx k, Real.sqrt_sq (Real.rpow_nonneg hx _)]

/-- `|ξ^α| ≤ (1 + |ξ|²)^{k/2}` for `|α| ≤ k`: the bound that puts `ξ^α ℱv` in `L²` whenever
`(1 + |ξ|²)^{k/2} ℱv` is. -/
theorem abs_xiPow_le_rpow {α : Fin d → ℕ} (hα : ∑ i, α i ≤ k) (ξ : EuclideanSpace ℝ (Fin d)) :
    |xiPow α ξ| ≤ (1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) := by
  have hb : (0 : ℝ) ≤ 1 + ‖ξ‖ ^ 2 := by positivity
  have h2 : |xiPow α ξ| ^ 2 ≤ ((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2)) ^ 2 := by
    rw [sq_rpow_half_natCast hb k, sq_abs]
    exact sq_xiPow_le_pow hα ξ
  exact le_of_pow_le_pow_left₀ two_ne_zero (Real.rpow_nonneg hb _) h2

/-- The sum `∑_{|α| ≤ k} |ξ^α|²` of the squared monomials of order at most `k`, the quantity
Exercise 7.4.2 compares with `(1 + |ξ|²)^{k/2}`. -/
noncomputable def xiPowSum (d k : ℕ) (ξ : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ α : MultiIndexLE (Fin d) k, xiPow α.1 ξ ^ 2

/-- The term of `∑_{|α| ≤ k} |ξ^α|²` at `α = 0` is `1`, so the sum is at least `1`. -/
theorem one_le_xiPowSum (ξ : EuclideanSpace ℝ (Fin d)) : 1 ≤ xiPowSum d k ξ := by
  have h0 : xiPow (0 : MultiIndexLE (Fin d) k).1 ξ ^ 2 = 1 := by simp [xiPow]
  rw [xiPowSum, ← h0]
  exact Finset.single_le_sum (f := fun α : MultiIndexLE (Fin d) k ↦ xiPow α.1 ξ ^ 2)
    (fun α _ ↦ sq_nonneg _) (Finset.mem_univ 0)

/-- The easy half of Exercise 7.4.2: each of the `#{α : |α| ≤ k}` terms of `∑_{|α| ≤ k} |ξ^α|²`
is at most `(1 + |ξ|²)^k`. -/
theorem xiPowSum_le (ξ : EuclideanSpace ℝ (Fin d)) :
    xiPowSum d k ξ ≤ (Fintype.card (MultiIndexLE (Fin d) k) : ℝ) * (1 + ‖ξ‖ ^ 2) ^ k := by
  rw [xiPowSum, ← Finset.card_univ, ← nsmul_eq_mul, ← Finset.sum_const]
  exact Finset.sum_le_sum fun α _ ↦ sq_xiPow_le_pow α.2 ξ

/-- The multi-index `k e_{i₀}`, the one whose monomial is `ξ_{i₀}^k`. -/
def topMultiIndex (k : ℕ) (i₀ : Fin d) : MultiIndexLE (Fin d) k :=
  ⟨fun i ↦ if i = i₀ then k else 0, by simp⟩

/-- The monomial of `k e_{i₀}` is `ξ_{i₀}^k`. -/
theorem xiPow_topMultiIndex (i₀ : Fin d) (ξ : EuclideanSpace ℝ (Fin d)) :
    xiPow (topMultiIndex k i₀).1 ξ = ξ i₀ ^ k := by
  have h1 : ∀ i : Fin d, i ≠ i₀ → ξ i ^ (topMultiIndex k i₀).1 i = 1 := by
    intro i hi
    simp [topMultiIndex, hi]
  rw [xiPow, Finset.prod_eq_single i₀ (fun i _ hi ↦ h1 i hi) (by simp)]
  simp [topMultiIndex]

/-- For `k ≥ 1` the sum `∑_{|α| ≤ k} |ξ^α|²` dominates its `α = 0` and `α = k e_{i₀}` terms. -/
theorem add_sq_xiPow_topMultiIndex_le (hk : k ≠ 0) (i₀ : Fin d)
    (ξ : EuclideanSpace ℝ (Fin d)) : 1 + (ξ i₀ ^ k) ^ 2 ≤ xiPowSum d k ξ := by
  classical
  have hne : (0 : MultiIndexLE (Fin d) k) ≠ topMultiIndex k i₀ := by
    intro h
    have hval := congrFun (congrArg Subtype.val h) i₀
    simp [topMultiIndex] at hval
    exact hk hval.symm
  have hle := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun α : MultiIndexLE (Fin d) k ↦ xiPow α.1 ξ ^ 2)
    (Finset.subset_univ ({0, topMultiIndex k i₀} : Finset (MultiIndexLE (Fin d) k)))
    (fun α _ _ ↦ sq_nonneg _)
  have h0 : xiPow (0 : MultiIndexLE (Fin d) k).1 ξ ^ 2 = 1 := by simp [xiPow]
  rw [Finset.sum_pair hne, h0, xiPow_topMultiIndex] at hle
  exact hle

/-- The hard half of Exercise 7.4.2: `(1 + |ξ|²)^k ≤ (1 + d)^k ∑_{|α| ≤ k} |ξ^α|²`. With
`a = ξ_{i₀}²` at a coordinate of largest absolute value, `|ξ|² ≤ d a`, and
`(1 + d a)^k ≤ (1 + d)^k max(1, a)^k ≤ (1 + d)^k (1 + a^k)`, whose two summands are the terms of
the sum at `α = 0` and at `α = k e_{i₀}`. No multinomial expansion is needed. -/
theorem pow_one_add_norm_sq_le (d k : ℕ) (ξ : EuclideanSpace ℝ (Fin d)) :
    (1 + ‖ξ‖ ^ 2) ^ k ≤ ((1 : ℝ) + d) ^ k * xiPowSum d k ξ := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simpa using one_le_xiPowSum (k := 0) ξ
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have hξ : ‖ξ‖ = 0 := by simp [EuclideanSpace.norm_eq]
    rw [hξ]
    have h1 := one_le_xiPowSum (d := 0) (k := k) ξ
    have h2 : (1 : ℝ) ≤ ((1 : ℝ) + (0 : ℕ)) ^ k := by norm_num
    calc (1 + (0 : ℝ) ^ 2) ^ k = 1 := by norm_num
      _ ≤ ((1 : ℝ) + (0 : ℕ)) ^ k * xiPowSum 0 k ξ := by nlinarith
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin d))
    (fun i ↦ ξ i ^ 2) ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  have ha0 : (0 : ℝ) ≤ ξ i₀ ^ 2 := sq_nonneg _
  have hnorm : ‖ξ‖ ^ 2 ≤ (d : ℝ) * ξ i₀ ^ 2 := by
    rw [← sum_sq_apply ξ]
    calc ∑ i, ξ i ^ 2 ≤ ∑ _i : Fin d, ξ i₀ ^ 2 :=
          Finset.sum_le_sum fun i _ ↦ hi₀ i (Finset.mem_univ i)
      _ = (d : ℝ) * ξ i₀ ^ 2 := by simp
  have hmax : 1 + (d : ℝ) * ξ i₀ ^ 2 ≤ (1 + d) * max 1 (ξ i₀ ^ 2) := by
    have h1 : (1 : ℝ) ≤ max 1 (ξ i₀ ^ 2) := le_max_left _ _
    have h2 : ξ i₀ ^ 2 ≤ max 1 (ξ i₀ ^ 2) := le_max_right _ _
    have h3 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith
  have hmaxk : (max 1 (ξ i₀ ^ 2)) ^ k ≤ 1 + (ξ i₀ ^ 2) ^ k := by
    rcases le_total (ξ i₀ ^ 2) 1 with h | h
    · rw [max_eq_left h, one_pow]
      have : (0 : ℝ) ≤ (ξ i₀ ^ 2) ^ k := by positivity
      linarith
    · rw [max_eq_right h]
      linarith [zero_le_one (α := ℝ)]
  have hlow : 1 + (ξ i₀ ^ 2) ^ k ≤ xiPowSum d k ξ := by
    calc 1 + (ξ i₀ ^ 2) ^ k = 1 + (ξ i₀ ^ k) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ xiPowSum d k ξ := add_sq_xiPow_topMultiIndex_le hk.ne' i₀ ξ
  calc (1 + ‖ξ‖ ^ 2) ^ k ≤ (1 + (d : ℝ) * ξ i₀ ^ 2) ^ k :=
        pow_le_pow_left₀ (by positivity) (by linarith) _
    _ ≤ ((1 + (d : ℝ)) * max 1 (ξ i₀ ^ 2)) ^ k := pow_le_pow_left₀ (by positivity) hmax _
    _ = (1 + (d : ℝ)) ^ k * (max 1 (ξ i₀ ^ 2)) ^ k := by rw [mul_pow]
    _ ≤ (1 + (d : ℝ)) ^ k * xiPowSum d k ξ :=
        mul_le_mul_of_nonneg_left (hmaxk.trans hlow) (by positivity)

/-- **Exercise 7.4.2**: there are `c₁, c₂ > 0` with
`c₁ (∑_{|α| ≤ k} |ξ^α|²)^{1/2} ≤ (1 + |ξ|²)^{k/2} ≤ c₂ (∑_{|α| ≤ k} |ξ^α|²)^{1/2}` for every
`ξ ∈ ℝ^d`. This is the two-sided symbol inequality that turns Plancherel's identity into the norm
equivalence (7.4.1); the constants are `c₁ = #{α : |α| ≤ k}^{-1/2}` and `c₂ = (1 + d)^{k/2}`. -/
theorem exercise_7_4_2 (d k : ℕ) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ ξ : EuclideanSpace ℝ (Fin d),
        c₁ * Real.sqrt (∑ α : MultiIndexLE (Fin d) k, |xiPow α.1 ξ| ^ 2)
            ≤ (1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2)
          ∧ (1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2)
            ≤ c₂ * Real.sqrt (∑ α : MultiIndexLE (Fin d) k, |xiPow α.1 ξ| ^ 2) := by
  have hne : Nonempty (MultiIndexLE (Fin d) k) := ⟨0⟩
  have hMpos : (0 : ℝ) < (Fintype.card (MultiIndexLE (Fin d) k) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  refine ⟨(Real.sqrt (Fintype.card (MultiIndexLE (Fin d) k) : ℝ))⁻¹,
    Real.sqrt (((1 : ℝ) + d) ^ k), inv_pos.2 (Real.sqrt_pos.2 hMpos),
    Real.sqrt_pos.2 (by positivity), fun ξ ↦ ?_⟩
  have hb : (0 : ℝ) ≤ 1 + ‖ξ‖ ^ 2 := by positivity
  have hS : (∑ α : MultiIndexLE (Fin d) k, |xiPow α.1 ξ| ^ 2) = xiPowSum d k ξ :=
    Finset.sum_congr rfl fun α _ ↦ sq_abs _
  rw [hS, rpow_half_eq_sqrt_pow hb k]
  refine ⟨?_, ?_⟩
  · rw [inv_mul_le_iff₀ (Real.sqrt_pos.2 hMpos), ← Real.sqrt_mul hMpos.le]
    exact Real.sqrt_le_sqrt (xiPowSum_le ξ)
  · rw [← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (pow_one_add_norm_sq_le d k ξ)

end SymbolBounds

section NormEquivalence

variable {d k : ℕ}

/-- The `ℝ≥0∞` norm of a real multiple of a complex number, squared. -/
theorem enorm_sq_ofReal_mul (r : ℝ) (z : ℂ) :
    ‖(r : ℂ) * z‖ₑ ^ 2 = ENNReal.ofReal (r ^ 2) * ‖z‖ₑ ^ 2 := by
  rw [enorm_mul, mul_pow]
  congr 1
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Complex.norm_real, Real.norm_eq_abs,
    sq_abs]

/-- The `ℝ≥0∞` norm of a scalar multiple of a real multiple of a complex number, squared. -/
theorem enorm_sq_mul_ofReal_mul (c : ℂ) (r : ℝ) (z : ℂ) :
    ‖c * ((r : ℂ) * z)‖ₑ ^ 2 = ENNReal.ofReal (‖c‖ ^ 2 * r ^ 2) * ‖z‖ₑ ^ 2 := by
  rw [enorm_mul, enorm_mul, mul_pow, mul_pow, ENNReal.ofReal_mul (by positivity), mul_assoc]
  congr 2
  · rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg c)]
  · rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Complex.norm_real, Real.norm_eq_abs,
      sq_abs]

/-- Plancherel's identity in the form of `eLpNorm`: the Fourier transform preserves the `L²`
seminorm of the representative. -/
theorem eLpNorm_fourier_eq (w : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    eLpNorm ((𝓕 w : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
        : EuclideanSpace ℝ (Fin d) → ℂ) 2 volume
      = eLpNorm (w : EuclideanSpace ℝ (Fin d) → ℂ) 2 volume := by
  have h := Lp.norm_fourier_eq w
  rw [Lp.norm_def, Lp.norm_def] at h
  exact (ENNReal.toReal_eq_toReal_iff' (Lp.eLpNorm_ne_top _) (Lp.eLpNorm_ne_top _)).1 h

/-- The symbol of `∂^α` in the standard basis is the monomial `ξ^α`: `⟪ξ, e_i⟫ = ξ_i`, and the
tuple of directions naming `α` lists `e_i` exactly `α_i` times. -/
theorem lineSymbol_multiIndexTuple (α : Fin d → ℕ) (ξ : EuclideanSpace ℝ (Fin d)) :
    lineSymbol (multiIndexTuple (stdBasis d) α) ξ = ((xiPow α ξ : ℝ) : ℂ) := by
  rw [lineSymbol_apply,
    prod_multiIndexTuple (M := ℂ) (stdBasis d) α fun e ↦ ((inner ℝ ξ e : ℝ) : ℂ), xiPow,
    Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [show (inner ℝ ξ (stdBasis d i) : ℝ) = ξ i by
    simp [stdBasis, EuclideanSpace.inner_single_right], Complex.ofReal_pow]

/-- If `(1 + |ξ|²)^{k/2} ℱv` lies in `L²` then so does `ξ^α ℱv` for every `|α| ≤ k`, by
`abs_xiPow_le_rpow`. -/
theorem memLp_lineSymbol_mul_fourier
    {v : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))}
    (hF : MemLp (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (𝓕 v) ξ) 2
      (volume : Measure (EuclideanSpace ℝ (Fin d))))
    {α : Fin d → ℕ} (hα : ∑ i, α i ≤ k) :
    MemLp (fun ξ ↦ lineSymbol (multiIndexTuple (stdBasis d) α) ξ * (𝓕 v) ξ) 2
      (volume : Measure (EuclideanSpace ℝ (Fin d))) := by
  refine hF.mono ?_ ?_
  · exact ((hasTemperateGrowth_lineSymbol
      (multiIndexTuple (stdBasis d) α)).1.continuous.aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable _)
  · filter_upwards with ξ
    rw [norm_mul, norm_mul, lineSymbol_multiIndexTuple, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖ξ‖ ^ 2) _)]
    exact mul_le_mul_of_nonneg_right (abs_xiPow_le_rpow hα ξ) (norm_nonneg _)

/-- **Plancherel for one weak derivative.** For `v ∈ H^k(ℝ^d)` and `|α| ≤ k`,
`‖∂^α v‖²_{L²} = ∫ (2π)^{2|α|} |ξ^α|² |ℱv(ξ)|² dξ`. -/
theorem sq_eLpNorm_weakDeriv {v w : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))}
    {α : Fin d → ℕ} (hα : ∑ i, α i ≤ k)
    (hF : MemLp (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (𝓕 v) ξ) 2
      (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hvw : HasWeakIteratedLineDerivOn (multiIndexTuple (stdBasis d) α)
      (v : EuclideanSpace ℝ (Fin d) → ℂ) (w : EuclideanSpace ℝ (Fin d) → ℂ) ⊤ volume) :
    eLpNorm (w : EuclideanSpace ℝ (Fin d) → ℂ) 2 volume ^ 2
      = ∫⁻ ξ, ENNReal.ofReal ((2 * Real.pi) ^ (2 * (∑ i, α i)) * xiPow α ξ ^ 2)
          * ‖(𝓕 v) ξ‖ₑ ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin d))) := by
  have hae := fourier_weakDeriv_aeEq (multiIndexTuple (stdBasis d) α)
    (Lp.iteratedLineDerivOp_eq_of_hasWeakIteratedLineDerivOn hvw)
    (memLp_lineSymbol_mul_fourier hF hα)
  rw [← eLpNorm_fourier_eq w, sq_eLpNorm_two (Lp.aestronglyMeasurable _)]
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with ξ hξ
  rw [hξ, lineSymbol_multiIndexTuple, enorm_sq_mul_ofReal_mul]
  congr 2
  rw [norm_pow, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg Real.pi_pos.le, mul_one, ← pow_mul]
  ring

/-- The full Fourier symbol `∑_{|α| ≤ k} |(2π ξ)^α|²` of the `H^k` norm: by Plancherel,
`∑_{|α| ≤ k} ‖∂^α v‖²_{L²} = ∫ (∑_{|α| ≤ k} (2π)^{2|α|} |ξ^α|²) |ℱv|²`. -/
noncomputable def fullSymbol (d k : ℕ) (ξ : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ α : MultiIndexLE (Fin d) k, (2 * Real.pi) ^ (2 * (∑ i, α.1 i)) * xiPow α.1 ξ ^ 2

/-- `1 ≤ 2π`. -/
theorem one_le_two_pi : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.two_le_pi]

/-- The full symbol is continuous. -/
theorem continuous_fullSymbol (d k : ℕ) :
    Continuous (fun ξ : EuclideanSpace ℝ (Fin d) ↦ fullSymbol d k ξ) :=
  continuous_finsetSum _ fun α _ ↦ continuous_const.mul ((continuous_xiPow α.1).pow 2)

/-- Every factor `(2π)^{2|α|}` is at least `1`, so the full symbol dominates `∑_{|α| ≤ k}
|ξ^α|²`. -/
theorem xiPowSum_le_fullSymbol (ξ : EuclideanSpace ℝ (Fin d)) :
    xiPowSum d k ξ ≤ fullSymbol d k ξ := by
  refine Finset.sum_le_sum fun α _ ↦ ?_
  nlinarith [one_le_pow₀ (n := 2 * (∑ i, α.1 i)) one_le_two_pi, sq_nonneg (xiPow α.1 ξ)]

/-- Every factor `(2π)^{2|α|}` is at most `(2π)^{2k}`. -/
theorem fullSymbol_le_xiPowSum (ξ : EuclideanSpace ℝ (Fin d)) :
    fullSymbol d k ξ ≤ (2 * Real.pi) ^ (2 * k) * xiPowSum d k ξ := by
  rw [xiPowSum, Finset.mul_sum]
  refine Finset.sum_le_sum fun α _ ↦ ?_
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ one_le_two_pi (Nat.mul_le_mul_left 2 α.2)) (sq_nonneg _)

/-- One half of the symbol comparison: `(1 + |ξ|²)^k ≤ (1 + d)^k ∑_{|α| ≤ k} |(2π ξ)^α|²`. -/
theorem pow_le_fullSymbol (ξ : EuclideanSpace ℝ (Fin d)) :
    (1 + ‖ξ‖ ^ 2) ^ k ≤ ((1 : ℝ) + d) ^ k * fullSymbol d k ξ :=
  (pow_one_add_norm_sq_le d k ξ).trans
    (mul_le_mul_of_nonneg_left (xiPowSum_le_fullSymbol ξ) (by positivity))

/-- The other half of the symbol comparison:
`∑_{|α| ≤ k} |(2π ξ)^α|² ≤ (2π)^{2k} #{α : |α| ≤ k} (1 + |ξ|²)^k`. -/
theorem fullSymbol_le_pow (ξ : EuclideanSpace ℝ (Fin d)) :
    fullSymbol d k ξ ≤ ((2 * Real.pi) ^ (2 * k)
      * (Fintype.card (MultiIndexLE (Fin d) k) : ℝ)) * (1 + ‖ξ‖ ^ 2) ^ k := by
  rw [mul_assoc]
  exact (fullSymbol_le_xiPowSum ξ).trans
    (mul_le_mul_of_nonneg_left (xiPowSum_le ξ) (by positivity))

/-- The integrand of the Fourier-side quadratic form is a.e.-measurable. -/
theorem aemeasurable_symbol_mul {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : Continuous g)
    (v : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    AEMeasurable (fun ξ ↦ ENNReal.ofReal (g ξ) * ‖(𝓕 v) ξ‖ₑ ^ 2)
      (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
  (ENNReal.measurable_ofReal.comp hg.measurable).aemeasurable.mul
    ((Lp.aestronglyMeasurable (𝓕 v)).enorm.pow_const 2)

/-- `‖(1 + |ξ|²)^{k/2} ℱv‖²_{L²} = ∫ (1 + |ξ|²)^k |ℱv|²`. -/
theorem sq_eLpNorm_symbol_mul_fourier
    (v : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (𝓕 v) ξ) 2 volume ^ 2
      = ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ k) * ‖(𝓕 v) ξ‖ₑ ^ 2
          ∂(volume : Measure (EuclideanSpace ℝ (Fin d))) := by
  have hcont : Continuous fun ξ : EuclideanSpace ℝ (Fin d) ↦
      (((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((continuous_const.add (continuous_norm.pow 2)).rpow_const
      fun _ ↦ Or.inr (by positivity))
  have hmeas : AEStronglyMeasurable
      (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (𝓕 v) ξ)
      (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
    hcont.aestronglyMeasurable.mul (Lp.aestronglyMeasurable _)
  rw [sq_eLpNorm_two hmeas]
  refine lintegral_congr fun ξ ↦ ?_
  rw [enorm_sq_ofReal_mul, sq_rpow_half_natCast (by positivity : (0 : ℝ) ≤ 1 + ‖ξ‖ ^ 2) k]

/-- **Plancherel for the whole Sobolev norm**: `∑_{|α| ≤ k} ‖∂^α v‖²_{L²}` is the integral of the
full symbol against `|ℱv|²`. -/
theorem sq_eLpNorm_sum
    {v : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))}
    {w : MultiIndexLE (Fin d) k → Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))}
    (hF : MemLp (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (𝓕 v) ξ) 2
      (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hw : ∀ α : MultiIndexLE (Fin d) k, HasWeakIteratedLineDerivOn
      (multiIndexTuple (stdBasis d) α.1) (v : EuclideanSpace ℝ (Fin d) → ℂ)
      (w α : EuclideanSpace ℝ (Fin d) → ℂ) ⊤ volume) :
    ∑ α : MultiIndexLE (Fin d) k, eLpNorm (w α : EuclideanSpace ℝ (Fin d) → ℂ) 2 volume ^ 2
      = ∫⁻ ξ, ENNReal.ofReal (fullSymbol d k ξ) * ‖(𝓕 v) ξ‖ₑ ^ 2
          ∂(volume : Measure (EuclideanSpace ℝ (Fin d))) := by
  rw [Finset.sum_congr rfl (fun α _ ↦ sq_eLpNorm_weakDeriv α.2 hF (hw α)),
    ← lintegral_finsetSum' _ (fun α _ ↦ aemeasurable_symbol_mul
      (continuous_const.mul ((continuous_xiPow α.1).pow 2)) v)]
  refine lintegral_congr fun ξ ↦ ?_
  rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun α _ ↦ by positivity)]
  rfl

/-- **(7.4.1)** for the complex-valued functions that §7.4 allows throughout: there are
`c₁, c₂ > 0` with

`c₁ ‖v‖_{H^k(ℝ^d)} ≤ ‖(1 + |ξ|²)^{k/2} ℱv‖_{L²(ℝ^d)} ≤ c₂ ‖v‖_{H^k(ℝ^d)}`

for every `v ∈ H^k(ℝ^d)`, the left-hand norm being the one Definition 7.2.2 displays,
`[∑_{|α| ≤ k} ‖∂^α v‖²_{L²}]^{1/2}`, which is the norm of
`SobolevMultiIndex ℂ (stdBasis d) k 2 ⊤ volume` by `SobolevMultiIndex.norm_eq_sum`
(`definition_7_2_2_multiIndex_norm` is that display for real-valued functions). The hypothesis is
that the family `w` consists of the weak derivatives `∂^α v` of Definition 7.1.3, which — `v` and
each `w α` lying in `L²(ℝ^d)` — is exactly membership of `H^k(ℝ^d)`.

The proof is Plancherel applied to each `∂^α v` (whose Fourier transform is `(2πi ξ)^α ℱv`, by
`sq_eLpNorm_weakDeriv`) followed by the symbol inequality of Exercise 7.4.2. The constants are
`c₁ = ((2π)^{2k} #{α : |α| ≤ k})^{-1/2}` and `c₂ = (1 + d)^{k/2}`. -/
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
                volume).toReal ≤ c₂ * (∑ α, ‖w α‖ ^ 2) ^ ((1 : ℝ) / 2) := by
  have hne : Nonempty (MultiIndexLE (Fin d) k) := ⟨0⟩
  have hMpos : (0 : ℝ) < (Fintype.card (MultiIndexLE (Fin d) k) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have ha1 : (0 : ℝ) < ((2 * Real.pi) ^ (2 * k)
      * (Fintype.card (MultiIndexLE (Fin d) k) : ℝ))⁻¹ := by positivity
  have ha2 : (0 : ℝ) < ((1 : ℝ) + d) ^ k := by positivity
  refine ⟨Real.sqrt (((2 * Real.pi) ^ (2 * k)
      * (Fintype.card (MultiIndexLE (Fin d) k) : ℝ))⁻¹), Real.sqrt (((1 : ℝ) + d) ^ k),
    Real.sqrt_pos.2 ha1, Real.sqrt_pos.2 ha2, ?_⟩
  intro v w hw
  obtain ⟨N, hN⟩ : ∃ N : ℝ≥0∞, N = eLpNorm
      (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (𝓕 v) ξ) 2 volume := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ≥0∞, A = ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ k) * ‖(𝓕 v) ξ‖ₑ ^ 2
      ∂(volume : Measure (EuclideanSpace ℝ (Fin d))) := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ≥0∞, B = ∫⁻ ξ, ENNReal.ofReal (fullSymbol d k ξ) * ‖(𝓕 v) ξ‖ₑ ^ 2
      ∂(volume : Measure (EuclideanSpace ℝ (Fin d))) := ⟨_, rfl⟩
  rw [← hN]
  have hres : ((⊤ : Opens (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d)))
      = Set.univ := rfl
  have hv : MemSobolevMultiIndex (stdBasis d) (v : EuclideanSpace ℝ (Fin d) → ℂ) k 2 ⊤ volume := by
    refine ⟨?_, fun α hα ↦ ⟨(w ⟨α, hα⟩ : EuclideanSpace ℝ (Fin d) → ℂ), hw ⟨α, hα⟩, ?_⟩⟩
    · rw [hres, Measure.restrict_univ]; exact Lp.memLp v
    · rw [hres, Measure.restrict_univ]; exact Lp.memLp (w ⟨α, hα⟩)
  have hF : MemLp (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (𝓕 v) ξ) 2 volume :=
    (theorem_7_4_1_complex v).1 hv
  have hA : N ^ 2 = A := by rw [hN, hAdef]; exact sq_eLpNorm_symbol_mul_fourier v
  have hB : ∑ α : MultiIndexLE (Fin d) k, eLpNorm (w α : EuclideanSpace ℝ (Fin d) → ℂ) 2 volume ^ 2
      = B := by rw [hBdef]; exact sq_eLpNorm_sum hF hw
  have hcomp1 : ENNReal.ofReal (((2 * Real.pi) ^ (2 * k)
      * (Fintype.card (MultiIndexLE (Fin d) k) : ℝ))⁻¹) * B ≤ A := by
    rw [hAdef, hBdef, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun ξ ↦ ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul ha1.le]
    gcongr
    calc ((2 * Real.pi) ^ (2 * k) * (Fintype.card (MultiIndexLE (Fin d) k) : ℝ))⁻¹
          * fullSymbol d k ξ
        ≤ ((2 * Real.pi) ^ (2 * k) * (Fintype.card (MultiIndexLE (Fin d) k) : ℝ))⁻¹
          * (((2 * Real.pi) ^ (2 * k) * (Fintype.card (MultiIndexLE (Fin d) k) : ℝ))
            * (1 + ‖ξ‖ ^ 2) ^ k) :=
          mul_le_mul_of_nonneg_left (fullSymbol_le_pow ξ) ha1.le
      _ = (1 + ‖ξ‖ ^ 2) ^ k := by field_simp
  have hcomp2 : A ≤ ENNReal.ofReal (((1 : ℝ) + d) ^ k) * B := by
    rw [hAdef, hBdef, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun ξ ↦ ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul ha2.le]
    gcongr
    exact pow_le_fullSymbol ξ
  have hAfin : A ≠ ⊤ := by rw [← hA, hN]; exact ENNReal.pow_ne_top hF.eLpNorm_lt_top.ne
  have hBfin : B ≠ ⊤ := by
    rw [← hB]
    exact (ENNReal.sum_lt_top.2 fun α _ ↦
      ENNReal.pow_lt_top (Lp.eLpNorm_ne_top (w α)).lt_top).ne
  have hPsum : ∑ α : MultiIndexLE (Fin d) k, ‖w α‖ ^ 2 = B.toReal := by
    rw [← hB, ENNReal.toReal_sum fun α _ ↦ ENNReal.pow_ne_top (Lp.eLpNorm_ne_top (w α))]
    exact Finset.sum_congr rfl fun α _ ↦ by rw [Lp.norm_def, ← ENNReal.toReal_pow]
  have hNsq : N.toReal ^ 2 = A.toReal := by rw [← ENNReal.toReal_pow, hA]
  have hsumnn : (0 : ℝ) ≤ ∑ α : MultiIndexLE (Fin d) k, ‖w α‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hP2 : ((∑ α : MultiIndexLE (Fin d) k, ‖w α‖ ^ 2) ^ ((1 : ℝ) / 2)) ^ 2
      = ∑ α : MultiIndexLE (Fin d) k, ‖w α‖ ^ 2 := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hsumnn]
    norm_num
  constructor
  · refine le_of_pow_le_pow_left₀ two_ne_zero ENNReal.toReal_nonneg ?_
    rw [mul_pow, Real.sq_sqrt ha1.le, hP2, hPsum, hNsq]
    have h := ENNReal.toReal_mono hAfin hcomp1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha1.le] at h
  · refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
    rw [mul_pow, Real.sq_sqrt ha2.le, hP2, hPsum, hNsq]
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBfin) hcomp2
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha2.le] at h

/-- Complexification preserves the `L²` norm. -/
theorem norm_ofRealCLM_compLp (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    ‖Complex.ofRealCLM.compLp f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  refine eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _) ?_
  filter_upwards [Complex.ofRealCLM.coeFn_compLp f] with x hx
  rw [hx]
  simp

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
  simpa only [norm_ofRealCLM_compLp] using key

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
(`SobolevEuclidean.exists_isCompactEmbedding_toContinuousMap_of_order`) — because the
backbone's extension operator exists at order one only (`theorem_7_3_5_universal` is open).
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

end AtkinsonHan.Chapter07
